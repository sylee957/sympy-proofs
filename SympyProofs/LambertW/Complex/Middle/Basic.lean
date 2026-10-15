import SympyProofs.LambertW.Complex.Basic
import SympyProofs.LambertW.RealLower

/-!
# Local complex middle branches

At each real input strictly between `-exp (-1)` and zero, `localMiddle` is
an analytic local inverse centered at the real lower value. Its values away
from the neighborhood of construction are unspecified. No global cut-domain
continuation or integer branch indexing is asserted here.
-/

open Set Filter Topology

namespace LambertW.Real

/-- Interior lower-branch values avoid the critical point. -/
theorem lower_lt_neg_one {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lower x < -1 := by
  simpa using strictAntiOn_lower
    (show -Real.exp (-1) ∈ Ico (-Real.exp (-1)) 0 from
      ⟨le_rfl, neg_neg_of_pos (Real.exp_pos (-1))⟩)
    ⟨hx.1.le, hx.2⟩ hx.1

end LambertW.Real

namespace LambertW.Complex

private theorem middle_ne_critical {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    (Real.lower x : ℂ) ≠ -1 := by
  intro h
  have hr := congrArg Complex.re h
  have hl := Real.lower_lt_neg_one hx
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hr
  linarith

/-- The local middle inverse centered at `x`, for `-exp (-1) < x < 0`. -/
noncomputable def localMiddle (x : ℝ) (hx : x ∈ Ioo (-Real.exp (-1)) 0) : ℂ → ℂ :=
  (analyticAt_mulExp (Real.lower x)).hasStrictDerivAt.localInverse mulExp
    (deriv mulExp (Real.lower x)) (Real.lower x)
    (deriv_mulExp_ne_zero (middle_ne_critical hx))

theorem analyticAt_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    AnalyticAt ℂ (localMiddle x hx) (x : ℂ) := by
  simpa only [localMiddle, mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩] using
    (analyticAt_mulExp (Real.lower x)).analyticAt_localInverse
      (deriv_mulExp_ne_zero (middle_ne_critical hx))

theorem eventually_localMiddle_mulExp {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ∀ᶠ w in 𝓝 (Real.lower x : ℂ), localMiddle x hx (mulExp w) = w :=
  (analyticAt_mulExp (Real.lower x)).hasStrictDerivAt.eventually_left_inverse
    (deriv_mulExp_ne_zero (middle_ne_critical hx))

theorem eventually_mulExp_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ∀ᶠ z in 𝓝 (x : ℂ), mulExp (localMiddle x hx z) = z := by
  simpa only [localMiddle, mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩] using
    (analyticAt_mulExp (Real.lower x)).hasStrictDerivAt.eventually_right_inverse
      (deriv_mulExp_ne_zero (middle_ne_critical hx))

@[simp] theorem localMiddle_center {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    localMiddle x hx (x : ℂ) = (Real.lower x : ℂ) := by
  simpa only [localMiddle, mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩] using
    (eventually_localMiddle_mulExp hx).self_of_nhds

theorem hasDerivAt_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    HasDerivAt (localMiddle x hx)
      (Complex.exp (Real.lower x) * (1 + (Real.lower x : ℂ)))⁻¹ (x : ℂ) := by
  simpa only [localMiddle, mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩, deriv_mulExp] using
    ((analyticAt_mulExp (Real.lower x)).hasStrictDerivAt.to_localInverse
      (deriv_mulExp_ne_zero (middle_ne_critical hx))).hasDerivAt

end LambertW.Complex
