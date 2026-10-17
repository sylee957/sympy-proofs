import SympyProofs.JordanKrylov.Algorithms.Operations
import Std.Tactic.Do
import Std.WP

/-! Algorithm 7: deterministic minimal annihilators, with bounded factor searches. -/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 7 on an indexed family, preserving the association between each
input vector and its annihilator for subsequent primary-generator computation.
`bound` bounds the exponent of `f`; `factors.toList.prod` is the cofactor `g`.
Correctness requires monic irreducibles and an annihilating product.
The bounded factor loop implements the paper's decreasing `i_max`. -/
def computeMinimalAnnihilatingPolynomials (K : Type*) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (bound : ℕ) (factors : Array K[X]) (e : Fin m → (Fin n → K)) :
    Array K[X] := Id.run do
  let mut cofactor := Operations.one
  for g in factors do
    cofactor := Operations.mul cofactor g
  let mut result : Array K[X] := #[]
  for i in List.finRange m do
    let mut b := Operations.applyMatrix cofactor A (e i)
    let mut b0 := e i
    let mut candidate := Operations.one
    -- Lines 3–12: extract the distinguished primary part.
    if b ≠ 0 then
      for j in List.range bound do
        b := Operations.applyMatrix f A b
        b0 := Operations.applyMatrix f A b0
        if b = 0 then
          candidate := Operations.pow f (j + 1)
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
        probe := Operations.applyMatrix g A probe
        if probe = 0 then
          b0 := Operations.applyMatrix g A b0
          candidate := Operations.mul candidate g
          iMax := ⟨j.val, Nat.le_trans (Nat.le_of_lt j.isLt) indexBound⟩
          break
    result := result.push candidate
  return result

open scoped Std.WP in
/-- Algorithm 7 returns one entry per input vector, regardless of the supplied
polynomial operations or factorization. -/
theorem computeMinimalAnnihilatingPolynomials_size
    (K : Type*) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (bound : ℕ)
    (factors : Array K[X]) (e : Fin m → (Fin n → K)) :
    (computeMinimalAnnihilatingPolynomials K A f bound factors e).size = m := by
  generalize h : computeMinimalAnnihilatingPolynomials K A f bound factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun _ _ _ => True
  · fun pref _ out => out.size = pref.length
  · fun _ _ _ => True
  · fun _ _ _ => True
  · fun _ _ _ => True
  · fun _ _ _ => True
  · fun _ _ _ => True
  all_goals simp_all [result]

end SympyProofs.JordanKrylov
