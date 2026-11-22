module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The principal complex cube root

The principal cube root and its cube equation, conjugation law, analyticity,
and continuity facts. This module is independent of the real cubic surd and
its complex extensions.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex
open scoped ComplexConjugate

/-- Principal complex cube root, used as a building block. -/
def principal (z : ℂ) : ℂ := z ^ (3⁻¹ : ℂ)

@[simp] theorem principal_cube (z : ℂ) : principal z ^ 3 = z :=
  Complex.cpow_nat_inv_pow z (by decide)

/-- On nonnegative real inputs the principal cube root is the real power. -/
theorem principal_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    principal (x : ℂ) = ((x ^ (3⁻¹ : ℝ) : ℝ) : ℂ) := by
  simpa [principal] using (Complex.ofReal_cpow hx (3⁻¹ : ℝ)).symm

/-- On negative real inputs the principal cube root has argument `π / 3`. -/
theorem principal_ofReal_of_neg {x : ℝ} (hx : x < 0) :
    principal (x : ℂ) = (((-x) ^ (3⁻¹ : ℝ) : ℝ) : ℂ) *
      ((1 + (Real.sqrt 3 : ℂ) * I) / 2) := by
  unfold principal
  rw [show (3⁻¹ : ℂ) = ((3⁻¹ : ℝ) : ℂ) by simp,
    Complex.cpow_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx,
    Complex.arg_ofReal_of_neg hx]
  simp only [← div_eq_mul_inv, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

theorem principal_conj_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    principal (conj z) = conj (principal z) := by
  have h := Complex.conj_cpow z (3⁻¹ : ℂ) (slitPlane_arg_ne_pi hz)
  simpa only [principal, map_inv₀, show conj (3 : ℂ) = 3 from Complex.conj_ofReal 3]
    using h

theorem analyticAt_principal {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ principal z :=
  analyticAt_id.cpow analyticAt_const hz

/-- The principal cube root is continuous even at zero on the closed right half-plane. -/
theorem continuousAt_principal_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    ContinuousAt principal z :=
  Complex.continuousAt_cpow_const_of_re_pos (Or.inl hz) (by norm_num)

/-- The real part of the principal cube root in polar form. -/
theorem principal_re (z : ℂ) :
    (principal z).re = ‖z‖ ^ (3⁻¹ : ℝ) * Real.cos (arg z / 3) := by
  have h := Complex.cpow_ofReal_re z (3⁻¹ : ℝ)
  rw [show ((3⁻¹ : ℝ) : ℂ) = (3⁻¹ : ℂ) by simp] at h
  rw [principal, h, div_eq_mul_inv]

/-- The imaginary part of the principal cube root in polar form. -/
theorem principal_im (z : ℂ) :
    (principal z).im = ‖z‖ ^ (3⁻¹ : ℝ) * Real.sin (arg z / 3) := by
  have h := Complex.cpow_ofReal_im z (3⁻¹ : ℝ)
  rw [show ((3⁻¹ : ℝ) : ℂ) = (3⁻¹ : ℂ) by simp] at h
  rw [principal, h, div_eq_mul_inv]

/-- Every principal cube root lies in the closed right half-plane. -/
theorem principal_re_nonneg (z : ℂ) : 0 ≤ (principal z).re := by
  have h := Complex.cpow_ofReal_re z (3⁻¹ : ℝ)
  rw [show ((3⁻¹ : ℝ) : ℂ) = (3⁻¹ : ℂ) by simp] at h
  rw [principal, h]
  refine mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
    (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
  · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
  · linarith [Complex.arg_le_pi z, Real.pi_pos]

/-- At a negative real, the principal cube root is continuous from above. -/
theorem continuousWithinAt_principal_of_neg {x : ℝ} (hx : x < 0) :
    ContinuousWithinAt principal {w : ℂ | 0 ≤ w.im} (x : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  have hlog : ContinuousWithinAt log {w : ℂ | 0 ≤ w.im} (x : ℂ) :=
    continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hx) (by simp)
  have h : ContinuousWithinAt (fun w => exp (log w * 3⁻¹)) {w : ℂ | 0 ≤ w.im} (x : ℂ) :=
    Complex.continuous_exp.continuousAt.comp_continuousWithinAt
      (hlog.mul continuousWithinAt_const)
  refine h.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hx0)] with w hw
    exact cpow_def_of_ne_zero hw _
  · exact cpow_def_of_ne_zero hx0 _

/-- The principal cube root is continuous on the closed upper half-plane,
including the negative real axis. -/
theorem continuousOn_principal_upper : ContinuousOn principal {z : ℂ | 0 ≤ z.im} := by
  intro z _
  by_cases hs : z ∈ slitPlane
  · exact (analyticAt_principal hs).continuousAt.continuousWithinAt
  · rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have hzr : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hs.2])
    rcases hs.1.lt_or_eq with hneg | h0
    · rw [← hzr]
      exact continuousWithinAt_principal_of_neg hneg
    · exact (continuousAt_principal_of_re_nonneg h0.ge).continuousWithinAt

private theorem arg_mem_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < arg z ∧ arg z < Real.pi :=
  ⟨lt_of_le_of_ne (arg_nonneg_iff.mpr hz.le) fun h => hz.ne' (arg_eq_zero_iff.mp h.symm).2,
    arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩

/-- In the open upper half-plane, the principal cube root has positive imaginary part. -/
theorem principal_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (principal z).im := by
  obtain ⟨h0, hpi⟩ := arg_mem_of_im_pos hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h := Complex.cpow_ofReal_im z (3⁻¹ : ℝ)
  rw [show ((3⁻¹ : ℝ) : ℂ) = (3⁻¹ : ℂ) by simp] at h
  rw [principal, h]
  refine mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _)
    (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · positivity
  · linarith [Real.pi_pos]

/-- In the open upper half-plane, the principal cube root has argument below `π / 3`. -/
theorem principal_im_lt_sqrt_three_mul_re {z : ℂ} (hz : 0 < z.im) :
    (principal z).im < Real.sqrt 3 * (principal z).re := by
  obtain ⟨h0, hpi⟩ := arg_mem_of_im_pos hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hre := Complex.cpow_ofReal_re z (3⁻¹ : ℝ)
  have him := Complex.cpow_ofReal_im z (3⁻¹ : ℝ)
  rw [show ((3⁻¹ : ℝ) : ℂ) = (3⁻¹ : ℂ) by simp] at hre him
  rw [principal, hre, him]
  have hn : 0 < ‖z‖ ^ (3⁻¹ : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
  have hs : 0 < Real.sin (Real.pi / 3 - arg z * 3⁻¹) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three] at hs
  nlinarith [mul_pos hn hs]

end RealCubeRoot
