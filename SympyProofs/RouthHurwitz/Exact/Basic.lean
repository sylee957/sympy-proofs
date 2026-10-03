import SympyProofs.RouthHurwitz.Exact.Domain
import SympyProofs.RouthHurwitz.Imperative.Basic

/-! Fraction-free arithmetic performed in the coefficient domain itself.
Sign normalization belongs to this numeric interface, not the unsigned core. -/
namespace RouthHurwitz.Exact
open Imperative Imperative.Bounds
variable {A : Type*} [CommRing A] [LinearOrder A] [Div A] [MulDivCancelClass A]

/-- Comparisons use the coefficient domain's linear order. Its real interpretation
is needed only by correctness proofs. All arithmetic, including quotients and
repairs, stays in `A`. -/
def run [IsStrictOrderedRing A] (p : Polynomial A) : Result A (width p.natDegree) := Id.run do
  let n := p.natDegree
  let coeff := p.coeff
  let W := width n
  have hW : 0 < W := width_pos n
  let mut upper := initialCoefficients n coeff 0
  if n = 0 then
    return { rows := [upper], signChanges := 0, degenerate := decide (coeff 0 = 0) }
  else
    let raw := initialCoefficients n coeff 1
    let (firstLower, valid) : Vector A W × Bool := repair n ⟨W, Nat.lt_succ_self W⟩ upper raw
    let mut lower := firstLower
    let mut rows := [upper, lower]
    let mut count : ℕ := if (upper[0] * lower[0]) < 0 then 1 else 0
    let mut degenerate := !valid
    let mut divisor := 1
    let mut nextDivisor := 1
    for k in List.range (n-1) do
      let w : Fin (W+1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
      let raw := Vector.ofFn (fun j : Fin W =>
        if hj : j.val < w then
          ((if lower[0] < 0 then (-1 : A) else 1) *
            (lower[0] * upper[j.val+1]'(next_index_lt n k j.val hj) -
              upper[0] * lower[j.val+1]'(next_index_lt n k j.val hj))) / divisor
        else 0)
      let (row, valid) : Vector A W × Bool := repair (n+1-(k+2)) w lower raw
      divisor := if raw[0] = 0 then 1 else nextDivisor
      nextDivisor := if raw[0] = 0 then 1 else |lower[0]|
      rows := List.append rows [row]
      count := count + if (lower[0] * row[0]) < 0 then 1 else 0
      degenerate := degenerate || !valid
      upper := lower
      lower := row
    return { rows := rows, signChanges := count, degenerate := degenerate }

end RouthHurwitz.Exact
