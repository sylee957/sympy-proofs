import SympyProofs.LambertW.Complex.Basic

/-! # The local principal inverse near zero -/

namespace LambertW.Complex

open Filter Topology

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
