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

end RealCubeRoot
