module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Norms
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed

/-! Derivatives of the nonsingular matrix inverse and its trace.
Invertibility is required only at the point of differentiation. No commutativity
between the matrix and its derivative is assumed. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open Filter
open scoped Topology

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}

/-- The scalar chain rule for matrix inversion: `(M⁻¹)' = -M⁻¹ * M' * M⁻¹`. -/
theorem hasDerivAt_inv (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    HasDerivAt (fun s => (M s)⁻¹) (-(M t)⁻¹ * M' * (M t)⁻¹) t := by
  open scoped Matrix.Norms.Operator in
    have hi : HasFDerivAt (fun B : Matrix n n 𝕜 => B⁻¹)
        (-ContinuousLinearMap.mulLeftRight 𝕜 (Matrix n n 𝕜) (M t)⁻¹ (M t)⁻¹)
        (M t) := by
      have hinv : (fun B : Matrix n n 𝕜 => B⁻¹) = Ring.inverse :=
        funext Matrix.nonsing_inv_eq_ringInverse
      rw [hinv]
      obtain ⟨u, hu⟩ := hunit
      rw [← hu]
      simpa only [Matrix.coe_units_inv] using hasFDerivAt_ringInverse (𝕜 := 𝕜) u
    simpa only [Function.comp_def, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      neg_mul] using! hi.comp_hasDerivAt t hM

/-- The inverse derivative stated entirely in terms of scalar derivatives of entries. -/
theorem hasDerivAt_inv_entrywise
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t)
    (hunit : IsUnit (M t)) :
    ∀ i j, HasDerivAt (fun s => (M s)⁻¹ i j) ((-(M t)⁻¹ * M' * (M t)⁻¹) i j) t := by
  exact hasDerivAt_iff_entrywise.mp
    (hasDerivAt_inv (hasDerivAt_iff_entrywise.mpr hM) hunit)

/-- Each entry of the inverse derivative is the corresponding entry of the
noncommutative matrix product. -/
theorem deriv_inv_apply
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t)
    (hunit : IsUnit (M t)) (i j : n) :
    deriv (fun s => (M s)⁻¹ i j) t = (-(M t)⁻¹ * M' * (M t)⁻¹) i j :=
  (hasDerivAt_inv_entrywise hM hunit i j).deriv

/-- The inverse derivative satisfies the remainder limit for every matrix norm. -/
theorem tendsto_inv_remainder_norm {F : Type*} [FunLike F (Matrix n n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix n n 𝕜)] [AddGroupNormClass F (Matrix n n 𝕜) ℝ]
    (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) (p : F) :
    Tendsto (fun s =>
      p ((M s)⁻¹ - (M t)⁻¹ - (s - t) • (-(M t)⁻¹ * M' * (M t)⁻¹)) / ‖s - t‖)
      (𝓝 t) (𝓝 0) :=
  (hasDerivAt_iff_tendsto_norm p).mp (hasDerivAt_inv hM hunit)

/-- A nonzero determinant supplies the invertibility hypothesis. -/
theorem hasDerivAt_inv_of_det_ne_zero (hM : HasDerivAt M M' t)
    (hdet : (M t).det ≠ 0) :
    HasDerivAt (fun s => (M s)⁻¹) (-(M t)⁻¹ * M' * (M t)⁻¹) t :=
  hasDerivAt_inv hM ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

theorem deriv_inv (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    deriv (fun s => (M s)⁻¹) t = -(M t)⁻¹ * M' * (M t)⁻¹ := by
  open scoped Matrix.Norms.Operator in
    simpa using! (hasDerivAt_inv hM hunit).deriv

/-- The inverse derivative for the symbolic matrix expression `t * X + Z`. -/
theorem hasDerivAt_inv_affine (X Z : Matrix n n 𝕜) (t : 𝕜)
    (hunit : IsUnit (t • X + Z)) :
    HasDerivAt (fun s : 𝕜 => (s • X + Z)⁻¹)
      (-(t • X + Z)⁻¹ * X * (t • X + Z)⁻¹) t :=
  hasDerivAt_inv (hasDerivAt_affine X Z t) hunit

theorem deriv_inv_affine (X Z : Matrix n n 𝕜) (t : 𝕜)
    (hunit : IsUnit (t • X + Z)) :
    deriv (fun s : 𝕜 => (s • X + Z)⁻¹) t =
      -(t • X + Z)⁻¹ * X * (t • X + Z)⁻¹ := by
  open scoped Matrix.Norms.Operator in
    simpa using! (hasDerivAt_inv_affine X Z t hunit).deriv

/-- The derivative of the trace of an inverse, with the minus sign outside the trace. -/
theorem hasDerivAt_trace_inv (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    HasDerivAt (fun s => Matrix.trace ((M s)⁻¹))
      (-Matrix.trace ((M t)⁻¹ * M' * (M t)⁻¹)) t := by
  simpa only [neg_mul, Matrix.trace_neg] using hasDerivAt_trace (hasDerivAt_inv hM hunit)

theorem deriv_trace_inv (hM : HasDerivAt M M' t) (hunit : IsUnit (M t)) :
    deriv (fun s => Matrix.trace ((M s)⁻¹)) t =
      -Matrix.trace ((M t)⁻¹ * M' * (M t)⁻¹) :=
  (hasDerivAt_trace_inv hM hunit).deriv

end SympyProofs.MatrixDerivative
