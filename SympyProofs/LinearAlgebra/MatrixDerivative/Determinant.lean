module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Scalar derivatives of determinants of finite square matrices. The column
replacement rule and Jacobi's adjugate formula hold even at singular matrices.
At nonsingular matrices, Jacobi's formula can also be written using the inverse. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- Differentiate a determinant by differentiating each column in turn. -/
theorem hasDerivAt_det_updateCol [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).det)
      (∑ j, ((M t).updateCol j (fun i => M' i j)).det) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun (σ : Equiv.Perm n) _ =>
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ =>
      hasDerivAt_iff_entrywise.mp hM (σ i) i)).const_mul ((Equiv.Perm.sign σ : ℤ) : 𝕜))
  simp_rw [Matrix.det_apply']
  refine h.congr_deriv ?_
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)).symm

theorem deriv_det_updateCol [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).det) t =
      ∑ j, ((M t).updateCol j (fun i => M' i j)).det :=
  (hasDerivAt_det_updateCol hM).deriv

/-- Jacobi's formula, valid without an invertibility assumption. -/
theorem hasDerivAt_det [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).det) (Matrix.trace ((M t).adjugate * M')) t := by
  refine (hasDerivAt_det_updateCol hM).congr_deriv ?_
  simp only [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem deriv_det [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).det) t = Matrix.trace ((M t).adjugate * M') :=
  (hasDerivAt_det hM).deriv

/-- At a nonsingular matrix, Jacobi's formula can be written using the inverse. -/
theorem hasDerivAt_det_of_isUnit [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    HasDerivAt (fun s => (M s).det)
      ((M t).det * Matrix.trace ((M t)⁻¹ * M')) t := by
  have hdet := (M t).isUnit_iff_isUnit_det.mp hunit
  have hadj : (M t).adjugate = (M t).det • (M t)⁻¹ := by
    calc
      (M t).adjugate = (M t).adjugate * M t * (M t)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (M t).det • (M t)⁻¹ := by
        rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine (hasDerivAt_det hM).congr_deriv ?_
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem deriv_det_of_isUnit [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    deriv (fun s => (M s).det) t = (M t).det * Matrix.trace ((M t)⁻¹ * M') :=
  (hasDerivAt_det_of_isUnit hM hunit).deriv

end SympyProofs.MatrixDerivative
