import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import SympyProofs.LambertW.RealPrincipal

/-!
# Local complex foundations for Lambert W

The entire forward map `mulExp` has its only critical point at `-1`.
Analytic local inverses exist at every noncritical point, by mathlib's
inverse function theorem. This module is shared by the complex branches.
-/

namespace LambertW.Complex

open Filter Topology

/-- The entire map inverted by the complex Lambert W branches. -/
noncomputable def mulExp (w : ℂ) : ℂ := w * Complex.exp w

@[simp] theorem mulExp_zero : mulExp 0 = 0 := by simp [mulExp]

@[simp] theorem mulExp_neg_one : mulExp (-1) = -Complex.exp (-1) := by simp [mulExp]

@[simp] theorem mulExp_ofReal (x : ℝ) : mulExp (x : ℂ) = (Real.mulExp x : ℂ) := by
  simp [mulExp, Real.mulExp, Complex.ofReal_exp]

theorem analyticAt_mulExp (w : ℂ) : AnalyticAt ℂ mulExp w :=
  analyticAt_id.mul analyticAt_cexp

/-- The forward map is entire. -/
theorem analyticOnNhd_mulExp : AnalyticOnNhd ℂ mulExp Set.univ :=
  fun w _ => analyticAt_mulExp w

theorem hasDerivAt_mulExp (w : ℂ) :
    HasDerivAt mulExp (Complex.exp w * (1 + w)) w := by
  convert (hasDerivAt_id w).mul (Complex.hasDerivAt_exp w) using 1
  · rfl
  · change Complex.exp w * (1 + w) = 1 * Complex.exp w + w * Complex.exp w
    ring

theorem deriv_mulExp (w : ℂ) : deriv mulExp w = Complex.exp w * (1 + w) :=
  (hasDerivAt_mulExp w).deriv

/-- The only critical point is `-1`; its image is `-exp (-1)`. -/
theorem deriv_mulExp_eq_zero_iff (w : ℂ) : deriv mulExp w = 0 ↔ w = -1 := by
  rw [deriv_mulExp, mul_eq_zero]
  simp only [Complex.exp_ne_zero, false_or]
  constructor <;> intro h <;> linear_combination h

theorem deriv_mulExp_ne_zero {w : ℂ} (hw : w ≠ -1) : deriv mulExp w ≠ 0 :=
  (deriv_mulExp_eq_zero_iff w).not.mpr hw

@[simp] theorem deriv_mulExp_zero : deriv mulExp 0 = 1 := by simp [deriv_mulExp]

/-- An analytic local inverse at each noncritical point. -/
theorem exists_analytic_localInverse {w : ℂ} (hw : w ≠ -1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (mulExp w) ∧
      (∀ᶠ z in nhds w, g (mulExp z) = z) ∧
      (∀ᶠ z in nhds (mulExp w), mulExp (g z) = z) := by
  let h := analyticAt_mulExp w
  let hn := deriv_mulExp_ne_zero hw
  exact ⟨h.hasStrictDerivAt.localInverse mulExp (deriv mulExp w) w hn,
    h.analyticAt_localInverse hn, h.hasStrictDerivAt.eventually_left_inverse hn,
    h.hasStrictDerivAt.eventually_right_inverse hn⟩

end LambertW.Complex
