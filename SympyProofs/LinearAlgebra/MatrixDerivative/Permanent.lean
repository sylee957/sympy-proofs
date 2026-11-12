module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import SympyProofs.LinearAlgebra.Permanent

/-! Scalar derivatives of permanents of finite square matrices, using the
permanental adjugate from `LinearAlgebra.Permanent`. Both the trace and column
replacement formulas hold without a nonsingularity assumption. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- Differentiate a permanent by differentiating each column in turn. -/
theorem hasDerivAt_permanent_updateCol [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).permanent)
      (∑ j, ((M t).updateCol j (fun i => M' i j)).permanent) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun (σ : Equiv.Perm n) _ =>
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ =>
      hasDerivAt_iff_entrywise.mp hM (σ i) i))
  change HasDerivAt (fun s => ∑ σ : Equiv.Perm n, ∏ i, M s (σ i) i) _ t
  refine h.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Matrix.permanent_updateCol_eq_sum_perm, mul_comm]

theorem deriv_permanent_updateCol [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).permanent) t =
      ∑ j, ((M t).updateCol j (fun i => M' i j)).permanent :=
  (hasDerivAt_permanent_updateCol hM).deriv

/-- The permanent analogue of Jacobi's formula, valid also at singular matrices. -/
theorem hasDerivAt_permanent [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).permanent)
      (Matrix.trace ((M t).permanentalAdjugate * M')) t := by
  simpa only [Matrix.sum_permanent_updateCol_eq_trace] using hasDerivAt_permanent_updateCol hM

theorem deriv_permanent [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).permanent) t =
      Matrix.trace ((M t).permanentalAdjugate * M') :=
  (hasDerivAt_permanent hM).deriv

end SympyProofs.MatrixDerivative
