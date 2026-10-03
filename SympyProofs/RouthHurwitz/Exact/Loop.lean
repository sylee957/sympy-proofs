import SympyProofs.RouthHurwitz.Exact.Basic

/-! Proof-only descriptions of the mutable locals in the numeric exact loop. -/
namespace RouthHurwitz.Exact
open Imperative Imperative.Bounds
variable {A : Type*} [CommRing A] [LinearOrder A] [Div A] [MulDivCancelClass A]

namespace Proofs
abbrev Locals (A : Type*) (n : ℕ) := Vector A (width n) × Vector A (width n) ×
  List (Vector A (width n)) × ℕ × Bool × A × A

def start (n : ℕ) (coeff : ℕ → A) : Locals A n :=
  let upper := initialCoefficients n coeff 0
  let (lower, valid) := repair n ⟨width n, Nat.lt_succ_self _⟩ upper (initialCoefficients n coeff 1)
  (upper, lower, [upper, lower],
    if (upper[0]'(width_pos _) * lower[0]'(width_pos _)) < 0 then 1 else 0, !valid, 1, 1)

def step (n k : ℕ) (s : Locals A n) : Locals A n :=
  let (upper, lower, rows, count, deg, divisor, nextDivisor) := s
  let w : Fin (width n+1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      ((if (lower[0]'(width_pos _)) < 0 then (-1 : A) else 1) *
        (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
          upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj))) / divisor
    else 0)
  let (row, valid) := repair (n+1-(k+2)) w lower raw
  (lower, row, List.append rows [row],
    count + if (lower[0]'(width_pos _) * row[0]'(width_pos _)) < 0 then 1 else 0,
    deg || !valid,
    if raw[0]'(width_pos _) = 0 then 1 else nextDivisor,
    if raw[0]'(width_pos _) = 0 then 1 else
      |lower[0]'(width_pos _)|)

omit [MulDivCancelClass A] in
/-- Expose the inline runner as a fold for loop-invariant proofs. -/
theorem run_eq [IsStrictOrderedRing A] (p : Polynomial A) :
    run p = if p.natDegree = 0 then
      { rows := [initial p 0], signChanges := 0, degenerate := decide (p.coeff 0 = 0) }
    else
      let s := (List.range (p.natDegree-1)).foldl (fun s j => step p.natDegree j s)
        (start p.natDegree p.coeff)
      { rows := s.2.2.1, signChanges := s.2.2.2.1, degenerate := s.2.2.2.2.1 } := by
  simp only [run, List.forIn_pure_yield_eq_foldl]
  rfl

end Proofs
end RouthHurwitz.Exact
