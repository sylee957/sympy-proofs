import SympyProofs.JordanKrylov.Algorithms.MinimalAnnihilatingPolynomials

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Compute minimal annihilators for an indexed family from a full list of
irreducible factors, with repetitions encoding multiplicities. No distinguished
primary factor or preliminary polynomial evaluation is needed. -/
def computeBasisAnnihilators (K : Type*) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (factors : Array K[X]) (e : Fin m → (Fin n → K)) : Array K[X] := Id.run do
  let mut result : Array K[X] := #[]
  for i in List.finRange m do
    let mut b0 := e i
    let mut candidate := Operations.one
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

/-- The factor-only routine specializes Algorithm 7 at exponent bound zero. -/
theorem computeBasisAnnihilators_eq
    (K : Type*) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array K[X])
    (e : Fin m → (Fin n → K)) :
    computeBasisAnnihilators K A factors e =
      computeMinimalAnnihilatingPolynomials K A X 0 factors e := by
  simp [computeBasisAnnihilators, computeMinimalAnnihilatingPolynomials]

open scoped Std.WP in
/-- The factor-only routine preserves the number and order of input vectors. -/
theorem computeBasisAnnihilators_size
    (K : Type*) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array K[X])
    (e : Fin m → (Fin n → K)) :
    (computeBasisAnnihilators K A factors e).size = m := by
  rw [computeBasisAnnihilators_eq]
  exact computeMinimalAnnihilatingPolynomials_size K A X 0 factors e

end SympyProofs.JordanKrylov
