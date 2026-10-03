import SympyProofs.RouthHurwitz.Table.Basic

/-! Executable fixed-width Routh runner, repairs, and result. -/
namespace RouthHurwitz.Imperative

variable {K : Type*}

section Rows
variable [Ring K] [DecidableEq K]

/-- Linear scan restricted to indices known to lie inside the row. -/
def scan {W : ℕ} (w : Fin (W + 1)) (raw : Vector K W) : ℕ :=
  (List.finRange w.val).findIdx (fun j => decide (raw[j.val]'(by omega) ≠ 0))

/-- Nonempty rows and the active-prefix bound are encoded in the parameter types. -/
def repair {W : ℕ} (d : ℕ) (w : Fin (W + 2))
    (previous raw : Vector K (W + 1)) : Vector K (W + 1) × Bool := Id.run do
  let k := scan w raw
  if k < w then
    if raw[0] = 0 then
      let row := Vector.ofFn (fun j : Fin (W + 1) =>
        if h : j.val + k < w then raw[j.val] + (-1 : K) ^ k * raw[j.val + k]'(by omega)
        else raw[j.val])
      return (row, true)
    else
      return (raw, true)
  else
    return (Vector.ofFn (fun j : Fin (W + 1) => previous[j.val] * (d - 2 * j.val : ℕ)), false)

/-- Finite table with fixed-width rows and the accumulated count and degeneracy flag. -/
structure Result (K : Type*) (W : ℕ) where
  rows : List (Vector K W)
  signChanges : ℕ
  /-- A zero raw row occurred, or the input polynomial was zero. -/
  degenerate : Bool
  deriving Repr, DecidableEq

/-- Form a row from descending coefficients, padding beyond the degree with zero. -/
def initialCoefficients (n : ℕ) (coeff : ℕ → K) (parity : ℕ) : Vector K (width n) :=
  Vector.ofFn (fun j => if 2*j.val+parity ≤ n then coeff (n-(2*j.val+parity)) else 0)

/-- Read a polynomial at its actual degree. -/
def initial (p : Polynomial K) (parity : ℕ) : Vector K (width p.natDegree) :=
  initialCoefficients p.natDegree p.coeff parity

end Rows

namespace Bounds

theorem width_pos (n : ℕ) : 0 < width n := by simp [width]
theorem activeWidth_le (n i : ℕ) : activeWidth n i ≤ width n := Nat.sub_le _ _
theorem next_index_lt (n k j : ℕ) (h : j < activeWidth n (k + 2)) :
    j + 1 < width n := by
  dsimp [activeWidth] at h
  have : 0 < (k + 2) / 2 := by omega
  omega

end Bounds

open Bounds

variable [Field K] [LinearOrder K]

/-- Executable imperative table builder. Initialization, elimination, and
online diagnostic updates are written directly in this runner. -/
def run (p : Polynomial K) : Result K (width p.natDegree) := Id.run do
  let n := p.natDegree
  let W := width n
  have hW : 0 < W := width_pos n
  let mut upper := initial p 0
  if n = 0 then
    return { rows := [upper], signChanges := 0, degenerate := decide (p.coeff 0 = 0) }
  else
    let raw := initial p 1
    let (firstLower, valid) : Vector K W × Bool := repair n ⟨W, Nat.lt_succ_self W⟩ upper raw
    let mut lower := firstLower
    let mut rows := [upper, lower]
    let mut count : ℕ := if upper[0] / lower[0] < 0 then 1 else 0
    let mut degenerate := !valid
    for k in List.range (n - 1) do
      let w : Fin (width n + 1) := ⟨activeWidth n (k + 2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
      let raw := Vector.ofFn (fun j : Fin W =>
        if hj : j.val < w then
          (lower[0] * upper[j.val + 1]'(next_index_lt n k j.val hj) -
            upper[0] * lower[j.val + 1]'(next_index_lt n k j.val hj)) / lower[0]
        else 0)
      let (row, valid) : Vector K W × Bool := repair (n + 1 - (k + 2)) w lower raw
      rows := List.append rows [row]
      count := count + if lower[0] / row[0] < 0 then 1 else 0
      degenerate := degenerate || !valid
      upper := lower
      lower := row
    return { rows := rows, signChanges := count, degenerate := degenerate }

/-- Constant-time acceptance check using the accumulated state. -/
def accepts {W : ℕ} (result : Result K W) : Bool :=
  !result.degenerate && decide (result.signChanges = 0)

end RouthHurwitz.Imperative
