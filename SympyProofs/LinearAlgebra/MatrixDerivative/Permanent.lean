module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-! Scalar derivatives of permanents of finite square matrices. The derivative
is a sum of permanents, replacing one column at a time by its derivative.
No nonsingularity assumption is needed. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- Differentiate a permanent by differentiating each column in turn. -/
theorem hasDerivAt_permanent [Fintype n] [DecidableEq n]
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
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)).symm

theorem deriv_permanent [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).permanent) t =
      ∑ j, ((M t).updateCol j (fun i => M' i j)).permanent :=
  (hasDerivAt_permanent hM).deriv

end SympyProofs.MatrixDerivative
