module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.PrincipalLogarithm
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Matrix logarithms with imaginary parts in `(-π, π]`

Every invertible finite complex matrix has exactly one logarithm with spectrum
in the half-open strip. Negative real eigenvalues are allowed: their scalar
logarithms have imaginary part `π`. Zero eigenvalues are excluded by `IsUnit A`.

`halfOpenLog` agrees with `principalLog` on the slit-spectrum domain. The upper
boundary is not preserved by conjugation, so no unconditional conjugation or
adjoint identity is asserted for this extension.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A logarithm using the scalar convention `-π < im (log z) ≤ π`. -/
def IsHalfOpenLogarithm (A L : Matrix n n ℂ) : Prop :=
  exp L = A ∧ spectrum ℂ L ⊆ halfOpenStrip

/-- Existence and uniqueness on all invertible complex matrices, including
matrices with negative eigenvalues and matrices that are not diagonalizable. -/
theorem existsUnique_halfOpenLogarithm (A : Matrix n n ℂ) (hA : IsUnit A) :
    ∃! L : Matrix n n ℂ, IsHalfOpenLogarithm A L := by
  let e := (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] End ℂ (n → ℂ))
  obtain ⟨l, hl, hu⟩ := existsUnique_endHalfOpenLogarithm (e A) (hA.map e)
  refine ⟨e.symm l, ⟨?_, ?_⟩, ?_⟩
  · apply e.injective
    change Matrix.toLinAlgEquiv' (exp (e.symm l)) = e A
    rw [toLin_exp]
    simpa only [← show e = Matrix.toLinAlgEquiv' from rfl, AlgEquiv.apply_symm_apply] using hl.1
  · simpa only [AlgEquiv.spectrum_eq] using hl.2
  · intro L hL
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    apply hu
    constructor
    · rw [← toLin_exp, hL.1]
    · simpa only [AlgEquiv.spectrum_eq] using hL.2

/-- Invertibility is both necessary and sufficient for a half-open-strip logarithm. -/
theorem exists_halfOpenLogarithm_iff (A : Matrix n n ℂ) :
    (∃ L, IsHalfOpenLogarithm A L) ↔ IsUnit A := by
  constructor
  · rintro ⟨L, hL⟩
    rw [← hL.1]
    exact isUnit_exp L
  · intro hA
    exact (existsUnique_halfOpenLogarithm A hA).exists

/-- The half-open logarithm for invertible matrices, with value `0` on singular matrices.
Invertibility is required by its correctness theorems, not by this function. -/
noncomputable def halfOpenLog (A : Matrix n n ℂ) : Matrix n n ℂ := by
  classical
  exact if hA : IsUnit A then (existsUnique_halfOpenLogarithm A hA).choose else 0

theorem halfOpenLog_of_not_isUnit (A : Matrix n n ℂ) (hA : ¬IsUnit A) :
    halfOpenLog A = 0 := by
  simp only [halfOpenLog, dite_eq_right hA]

theorem halfOpenLog_spec (A : Matrix n n ℂ) (hA : IsUnit A) :
    IsHalfOpenLogarithm A (halfOpenLog A) := by
  simpa only [halfOpenLog, dite_eq_left hA] using
    (existsUnique_halfOpenLogarithm A hA).choose_spec.1

@[simp] theorem exp_halfOpenLog (A : Matrix n n ℂ) (hA : IsUnit A) :
    exp (halfOpenLog A) = A := (halfOpenLog_spec A hA).1

theorem spectrum_halfOpenLog (A : Matrix n n ℂ) (hA : IsUnit A) :
    spectrum ℂ (halfOpenLog A) ⊆ halfOpenStrip := (halfOpenLog_spec A hA).2

theorem halfOpenLog_unique (A L : Matrix n n ℂ) (hA : IsUnit A)
    (hL : IsHalfOpenLogarithm A L) : L = halfOpenLog A := by
  simpa only [halfOpenLog, dite_eq_left hA] using
    (existsUnique_halfOpenLogarithm A hA).choose_spec.2 L hL

/-- A certificate usable by `Logarithm.cpow` without a branch-cut restriction. -/
noncomputable def halfOpenLogarithm (A : Matrix n n ℂ) (hA : IsUnit A) : Logarithm A :=
  ⟨halfOpenLog A, exp_halfOpenLog A hA⟩

theorem HasSlitSpectrum.isUnit {A : Matrix n n ℂ} (hA : HasSlitSpectrum A) : IsUnit A := by
  apply spectrum.isUnit_of_zero_notMem ℂ
  intro hzero
  exact Complex.slitPlane_ne_zero (hA hzero) rfl

/-- The extension agrees with the open-strip principal logarithm on its domain. -/
theorem halfOpenLog_eq_principalLog (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    halfOpenLog A = principalLog A := by
  symm
  exact halfOpenLog_unique A _ hA.isUnit
    ⟨exp_principalLog A hA, (spectrum_principalLog A hA).trans principalStrip_subset_halfOpenStrip⟩

/-- The usual scalar logarithm gives the half-open logarithm of a diagonal matrix. -/
theorem halfOpenLog_diagonal (d : n → ℂ) (hA : IsUnit (Matrix.diagonal d)) :
    halfOpenLog (Matrix.diagonal d) = Matrix.diagonal (fun i => Complex.log (d i)) := by
  symm
  apply halfOpenLog_unique _ _ hA
  constructor
  · rw [exp_diagonal_complex]
    congr 1
    funext i
    apply Complex.exp_log
    intro hi
    apply spectrum.zero_notMem ℂ hA
    rw [spectrum_diagonal]
    exact ⟨i, hi⟩
  · rw [spectrum_diagonal]
    rintro _ ⟨i, rfl⟩
    exact log_mem_halfOpenStrip (d i)

/-- In particular, the chosen logarithm of `-I` is `π i I`. -/
theorem halfOpenLog_neg_one :
    halfOpenLog (-1 : Matrix n n ℂ) =
      (Real.pi * Complex.I) • (1 : Matrix n n ℂ) := by
  symm
  apply halfOpenLog_unique (-1 : Matrix n n ℂ) _ isUnit_one.neg
  constructor
  · rw [Matrix.smul_one_eq_diagonal, exp_diagonal_complex, ← Complex.log_neg_one]
    simp only [Complex.exp_log (neg_ne_zero.mpr one_ne_zero),
      ← Matrix.diagonal_neg, Matrix.diagonal_one]
  · rw [Matrix.smul_one_eq_diagonal, spectrum_diagonal]
    rintro _ ⟨i, rfl⟩
    simpa only [Complex.log_neg_one] using log_mem_halfOpenStrip (-1)

end SympyProofs.MatrixExponential
