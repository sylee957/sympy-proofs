module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Transpose
public import SympyProofs.LinearAlgebra.MatrixDerivative.Conjugate
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

import Mathlib.Analysis.Matrix.Normed

/-! The adjoint (conjugate transpose) commutes with differentiation by a real
parameter, for matrices with real or complex entries. For a complex-differentiable
matrix-valued function, its adjoint is complex differentiable at a point exactly
when the original derivative there is zero. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The real-parameter derivative of an adjoint is the adjoint of the derivative. -/
theorem hasDerivAt_adjoint {M : ℝ → Matrix m n 𝕜}
    {M' : Matrix m n 𝕜} {t : ℝ} (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s)ᴴ) M'ᴴ t :=
  hasDerivAt_conj (hasDerivAt_transpose hM)

theorem deriv_adjoint [Fintype m] [Fintype n] {M : ℝ → Matrix m n 𝕜}
    {M' : Matrix m n 𝕜} {t : ℝ} (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s)ᴴ) t = M'ᴴ := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_adjoint hM).deriv

/-- For a complex-differentiable matrix-valued function, the adjoint is complex
differentiable at a point exactly when the original derivative there is zero. -/
theorem differentiableAt_adjoint_iff_deriv_eq_zero
    {M : ℂ → Matrix m n ℂ} {M' : Matrix m n ℂ} {t : ℂ}
    (hM : HasDerivAt M M' t) :
    DifferentiableAt ℂ (fun s => (M s)ᴴ) t ↔ M' = 0 := by
  simpa only [Matrix.conjTranspose, RCLike.star_def, Matrix.transpose_eq_zero] using!
    differentiableAt_conj_iff_deriv_eq_zero (hasDerivAt_transpose hM)

/-- A nonzero complex derivative prevents the adjoint matrix function from
being complex differentiable. -/
theorem not_differentiableAt_adjoint
    {M : ℂ → Matrix m n ℂ} {M' : Matrix m n ℂ} {t : ℂ}
    (hM : HasDerivAt M M' t) (hne : M' ≠ 0) :
    ¬DifferentiableAt ℂ (fun s => (M s)ᴴ) t :=
  fun h => hne ((differentiableAt_adjoint_iff_deriv_eq_zero hM).mp h)

/-- In particular, the adjoint of `z • X + Z` is nowhere complex differentiable
when `X` is nonzero. This includes `z • I` in positive dimension. -/
theorem not_differentiableAt_adjoint_affine (X Z : Matrix n n ℂ) (t : ℂ) (hX : X ≠ 0) :
    ¬DifferentiableAt ℂ (fun s : ℂ => (s • X + Z)ᴴ) t :=
  not_differentiableAt_adjoint (hasDerivAt_affine X Z t) hX

end SympyProofs.MatrixDerivative
