import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations

/-! Algorithm 7: deterministic minimal annihilators, with bounded factor searches. -/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 7 on an indexed family, preserving the association between each
input vector and its annihilator for subsequent primary-generator computation.
`bound` bounds the exponent of `f`; `factors.toList.prod` is the cofactor `g`.
Correctness requires monic irreducibles and an annihilating product.
The bounded factor loop implements the paper's decreasing `i_max`. -/
def computeMinimalAnnihilatingPolynomials (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (bound : ℕ) (factors : Array K[X]) (e : Fin m → (Fin n → K)) :
    Array K[X] := Id.run do
  let mut cofactor := PolynomialOperations.one
  for g in factors do
    cofactor := PolynomialOperations.mul cofactor g
  let mut result : Array K[X] := #[]
  for i in List.finRange m do
    let mut b := PolynomialOperations.applyMatrix cofactor A (e i)
    let mut b0 := e i
    let mut candidate := PolynomialOperations.one
    -- Lines 3–12: extract the distinguished primary part.
    if b ≠ 0 then
      for j in List.range bound do
        b := PolynomialOperations.applyMatrix f A b
        b0 := PolynomialOperations.applyMatrix f A b0
        if b = 0 then
          candidate := PolynomialOperations.pow f (j + 1)
          break
    let mut iMax : { k : ℕ // k ≤ factors.size } := ⟨factors.size, Nat.le_refl _⟩
    -- Lines 13–23: at most q searches, each strictly decreasing iMax.
    for _ in factors do
      if iMax.val = 0 ∨ b0 = 0 then break
      let mut probe := b0
      -- Array index j represents the paper's factor index j + 1.
      have indexBound := iMax.property
      for j in List.finRange iMax.val do
        let g := factors[j.val]'(Nat.lt_of_lt_of_le j.isLt indexBound)
        probe := PolynomialOperations.applyMatrix g A probe
        if probe = 0 then
          b0 := PolynomialOperations.applyMatrix g A b0
          candidate := PolynomialOperations.mul candidate g
          iMax := ⟨j.val, Nat.le_trans (Nat.le_of_lt j.isLt) indexBound⟩
          break
    result := result.push candidate
  return result
end SympyProofs.JordanKrylov
