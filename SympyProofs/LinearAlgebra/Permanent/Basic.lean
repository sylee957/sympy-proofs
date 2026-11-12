module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Data.Matrix.Mul

/-! Algebraic identities for Mathlib's permanent of a finite square matrix. -/

@[expose] public section

namespace Matrix

variable {n : Type*}

/-- Expand each permutation product along a replaced column. -/
theorem permanent_updateCol_eq_sum_perm {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (j : n) (b : n → R) :
    (A.updateCol j b).permanent =
      ∑ σ : Equiv.Perm n, b (σ j) * ∏ k ∈ Finset.univ.erase j, A (σ k) k := by
  simp only [Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)

/-- The permanent is additive in any one column. -/
theorem permanent_updateCol_add {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (j : n) (u v : n → R) :
    (A.updateCol j (u + v)).permanent =
      (A.updateCol j u).permanent + (A.updateCol j v).permanent := by
  simp [permanent_updateCol_eq_sum_perm, add_mul, Finset.sum_add_distrib]

/-- The permanent is additive in any one row. -/
theorem permanent_updateRow_add {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (i : n) (u v : n → R) :
    (A.updateRow i (u + v)).permanent =
      (A.updateRow i u).permanent + (A.updateRow i v).permanent := by
  rw [← permanent_transpose, ← updateCol_transpose, permanent_updateCol_add,
    updateCol_transpose, updateCol_transpose, permanent_transpose, permanent_transpose]

/-- The permanent of an outer product, including the empty matrix case. -/
theorem permanent_vecMulVec {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (u v : n → R) :
    (vecMulVec u v).permanent =
      (Nat.factorial (Fintype.card n) : R) * (∏ i, u i) * (∏ j, v j) := by
  simp only [permanent, vecMulVec_apply, Finset.prod_mul_distrib]
  simp_rw [Equiv.prod_comp]
  simp [Fintype.card_perm, mul_assoc]

/-- The all-ones matrix has permanent `n!`, even though it has repeated rows. -/
theorem permanent_const_one {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] :
    permanent (fun _ _ : n => (1 : R)) = (Nat.factorial (Fintype.card n) : R) := by
  simp [permanent, Fintype.card_perm]

end Matrix
