module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Matrix.Normed

/-! Entrywise conjugation commutes with differentiation by a real parameter.
The matrix entries may be real or complex. Complex conjugation itself is nowhere
complex differentiable. For a complex-differentiable matrix-valued function,
its entrywise conjugate is complex differentiable at a point exactly when the
original derivative there is zero. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped ComplexConjugate

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- Conjugate each entry of the derivative when differentiating by a real scalar. -/
theorem hasDerivAt_conj {M : ℝ → Matrix m n 𝕜}
    {M' : Matrix m n 𝕜} {t : ℝ} (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s).map conj) (M'.map conj) t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  exact (hasDerivAt_iff_entrywise.mp hM i j).star

theorem deriv_conj [Fintype m] [Fintype n] {M : ℝ → Matrix m n 𝕜}
    {M' : Matrix m n 𝕜} {t : ℝ} (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s).map conj) t = M'.map conj := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_conj hM).deriv

private theorem deriv_eq_zero_of_hasDerivAt_scalar_conj {f : ℂ → ℂ} {a b z : ℂ}
    (hf : HasDerivAt f a z) (hg : HasDerivAt (fun w => conj (f w)) b z) : a = 0 := by
  have h := ((hf.hasFDerivAt.restrictScalars ℝ).star).unique
    (hg.hasFDerivAt.restrictScalars ℝ)
  have h1 : conj a = b := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) h
  have hI : -(Complex.I * b) = Complex.I * b := by
    simpa [h1] using congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) h
  have hb : b = 0 :=
    (mul_eq_zero.mp (CharZero.neg_eq_self_iff.mp hI)).resolve_left Complex.I_ne_zero
  simpa using congrArg conj (h1.trans hb)

private theorem hasDerivAt_scalar_conj_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : HasDerivAt f 0 z) : HasDerivAt (fun w => conj (f w)) 0 z := by
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_restrictScalars ℝ (hf.hasFDerivAt.restrictScalars ℝ).star
  ext w
  simp

/-- Scalar complex conjugation is nowhere complex differentiable. -/
theorem not_differentiableAt_scalar_conj (z : ℂ) :
    ¬DifferentiableAt ℂ (conj : ℂ → ℂ) z := by
  intro h
  exact one_ne_zero
    (deriv_eq_zero_of_hasDerivAt_scalar_conj (hasDerivAt_id z) h.hasDerivAt)

/-- For a complex-differentiable matrix-valued function, entrywise conjugation
preserves complex differentiability at a point exactly when its derivative is zero. -/
theorem differentiableAt_conj_iff_deriv_eq_zero
    {M : ℂ → Matrix m n ℂ} {M' : Matrix m n ℂ} {t : ℂ}
    (hM : HasDerivAt M M' t) :
    DifferentiableAt ℂ (fun s => (M s).map conj) t ↔ M' = 0 := by
  constructor
  · rintro ⟨L, hL⟩
    ext i j
    exact deriv_eq_zero_of_hasDerivAt_scalar_conj (hasDerivAt_iff_entrywise.mp hM i j)
      (hasDerivAt_iff_entrywise.mp hL.hasDerivAt i j)
  · intro hM'
    subst M'
    have h : HasDerivAt (fun s => (M s).map conj) 0 t := by
      apply hasDerivAt_iff_entrywise.mpr
      intro i j
      exact hasDerivAt_scalar_conj_zero (hasDerivAt_iff_entrywise.mp hM i j)
    exact ⟨_, h.hasFDerivAt⟩

/-- A nonzero complex derivative prevents the conjugated matrix function from
being complex differentiable. -/
theorem not_differentiableAt_conj
    {M : ℂ → Matrix m n ℂ} {M' : Matrix m n ℂ} {t : ℂ}
    (hM : HasDerivAt M M' t) (hne : M' ≠ 0) :
    ¬DifferentiableAt ℂ (fun s => (M s).map conj) t :=
  fun h => hne ((differentiableAt_conj_iff_deriv_eq_zero hM).mp h)

/-- In particular, the conjugate of `z • X + Z` is nowhere complex differentiable
when `X` is nonzero. This includes `z • I` in positive dimension. -/
theorem not_differentiableAt_conj_affine (X Z : Matrix n n ℂ) (t : ℂ) (hX : X ≠ 0) :
    ¬DifferentiableAt ℂ (fun s : ℂ => (s • X + Z).map conj) t :=
  not_differentiableAt_conj (hasDerivAt_affine X Z t) hX

end SympyProofs.MatrixDerivative
