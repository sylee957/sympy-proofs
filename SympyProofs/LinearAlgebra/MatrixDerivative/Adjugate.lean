module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Determinant
public import SympyProofs.LinearAlgebra.MatrixDerivative.Mul

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of the classical adjugate. The column replacement formula
holds at every matrix, including singular matrices. At nonsingular matrices it
can be expressed using the inverse and trace. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped Matrix

variable {𝕜 n : Type*} [RCLike 𝕜]

private theorem adjugate_apply_updateCol [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) (i j : n) :
    A.adjugate i j = (A.updateCol i (Pi.single j 1)).det := by
  calc
    A.adjugate i j = (Aᵀ).adjugate j i := by
      rw [← Matrix.adjugate_transpose]
      rfl
    _ = (A.updateCol i (Pi.single j 1)).det := by
      rw [Matrix.adjugate_apply, Matrix.updateRow_transpose, Matrix.det_transpose]

/-- Replace each column with its derivative, sum the resulting adjugates, and
subtract the original adjugate. Entry `(i, j)` of the adjugate is independent of
column `i`, so that term contributes the unchanged entry and must be subtracted.
No invertibility assumption is needed. -/
theorem hasDerivAt_adjugate [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).adjugate)
      ((∑ k, ((M t).updateCol k (fun a => M' a k)).adjugate) - (M t).adjugate) t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  have hcol : HasDerivAt (fun s => (M s).updateCol i (Pi.single j 1))
      (M'.updateCol i 0) t := by
    apply hasDerivAt_iff_entrywise.mpr
    intro a b
    by_cases hb : b = i
    · subst b
      simpa only [Matrix.updateCol_self, Pi.zero_apply] using
        hasDerivAt_const t ((Pi.single j 1 : n → 𝕜) a)
    · simpa only [Matrix.updateCol_ne hb] using hasDerivAt_iff_entrywise.mp hM a b
  simp_rw [adjugate_apply_updateCol (M _)]
  refine (hasDerivAt_det_updateCol hcol).congr_deriv ?_
  simp only [Matrix.sub_apply, Matrix.sum_apply]
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hzero : (((M t).updateCol i (Pi.single j 1)).updateCol i
      (fun a => (M'.updateCol i 0) a i)).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro a
    simp
  rw [hzero, add_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hki := Finset.ne_of_mem_erase hk
    simp only [Matrix.updateCol_ne hki, adjugate_apply_updateCol]
    rw [Matrix.updateCol_comm _ hki.symm]
  · simp only [adjugate_apply_updateCol, Matrix.updateCol_idem]

theorem deriv_adjugate [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).adjugate) t =
      (∑ k, ((M t).updateCol k (fun a => M' a k)).adjugate) - (M t).adjugate := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_adjugate hM).deriv

/-- At a nonsingular matrix, differentiate `M * adjugate M = det M • 1`
and solve for the derivative of the adjugate. The order of factors is preserved. -/
theorem hasDerivAt_adjugate_of_isUnit [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    HasDerivAt (fun s => (M s).adjugate)
      (Matrix.trace ((M t)⁻¹ * M') • (M t).adjugate -
        (M t)⁻¹ * M' * (M t).adjugate) t := by
  have hdet := (M t).isUnit_iff_isUnit_det.mp hunit
  have hadj : (M t).adjugate = (M t).det • (M t)⁻¹ := by
    calc
      (M t).adjugate = (M t).adjugate * M t * (M t)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (M t).det • (M t)⁻¹ := by
        rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hprod := hasDerivAt_mul hM (hasDerivAt_adjugate hM)
  have hid : HasDerivAt (fun s => M s * (M s).adjugate)
      (((M t).det * Matrix.trace ((M t)⁻¹ * M')) • (1 : Matrix n n 𝕜)) t := by
    simp_rw [Matrix.mul_adjugate]
    apply hasDerivAt_iff_entrywise.mpr
    intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (hasDerivAt_det_of_isUnit hM hunit).mul_const ((1 : Matrix n n 𝕜) i j)
  have heq := congrArg (fun B => (M t)⁻¹ * B) (by
    open scoped Matrix.Norms.Elementwise in
      exact hprod.unique hid)
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at heq
  convert (hasDerivAt_adjugate hM) using 1
  symm
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm, heq, hadj, smul_smul, mul_comm]

theorem deriv_adjugate_of_isUnit [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    deriv (fun s => (M s).adjugate) t =
      Matrix.trace ((M t)⁻¹ * M') • (M t).adjugate -
        (M t)⁻¹ * M' * (M t).adjugate := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_adjugate_of_isUnit hM hunit).deriv

end SympyProofs.MatrixDerivative
