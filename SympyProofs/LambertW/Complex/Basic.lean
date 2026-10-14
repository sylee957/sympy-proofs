import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import SympyProofs.LambertW.RealPrincipal

/-!
# Local complex foundations for Lambert W

The entire forward map `mulExp` has its only critical point at `-1`.
`localPrincipal` is an analytic inverse near zero, constructed using mathlib's
inverse function theorem. Its values away from this neighborhood are unspecified;
this module does not construct a global complex branch or choose branch cuts.
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

/-- The local principal inverse near zero, with no claims about values elsewhere. -/
noncomputable def localPrincipal : ℂ → ℂ :=
  (analyticAt_mulExp 0).hasStrictDerivAt.localInverse mulExp (deriv mulExp 0) 0
    (by simp)

theorem analyticAt_localPrincipal_zero : AnalyticAt ℂ localPrincipal 0 := by
  simpa [localPrincipal] using (analyticAt_mulExp 0).analyticAt_localInverse (by simp)

theorem eventually_localPrincipal_mulExp :
    ∀ᶠ w in nhds (0 : ℂ), localPrincipal (mulExp w) = w := by
  exact (analyticAt_mulExp 0).hasStrictDerivAt.eventually_left_inverse (by simp)

theorem eventually_mulExp_localPrincipal :
    ∀ᶠ z in nhds (0 : ℂ), mulExp (localPrincipal z) = z := by
  simpa [localPrincipal] using
    (analyticAt_mulExp 0).hasStrictDerivAt.eventually_right_inverse (by simp)

@[simp] theorem localPrincipal_zero : localPrincipal 0 = 0 := by
  simpa using eventually_localPrincipal_mulExp.self_of_nhds

theorem hasDerivAt_localPrincipal_zero : HasDerivAt localPrincipal 1 0 := by
  simpa [localPrincipal] using
    ((analyticAt_mulExp 0).hasStrictDerivAt.to_localInverse (by simp)).hasDerivAt

@[simp] theorem deriv_localPrincipal_zero : deriv localPrincipal 0 = 1 :=
  hasDerivAt_localPrincipal_zero.deriv

end LambertW.Complex
