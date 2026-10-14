import SympyProofs.LambertW.Complex.Analytic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Order

/-! # Taylor expansion of the principal branch at zero

The Taylor series converges throughout `‖z‖ < exp (-1)`. We compute its first
four coefficients and give the cubic expansion with an analytic remainder.
-/

namespace LambertW.Complex

open Set Filter Topology

theorem hasDerivAt_deriv_principal {z : ℂ} (hz : z ∈ principalDomain) :
    HasDerivAt (deriv principal)
      (-(Complex.exp (principal z) * (2 + principal z)) /
        (Complex.exp (principal z) * (1 + principal z)) ^ 3) z := by
  have hp := hasDerivAt_principal hz
  have he := (Complex.hasDerivAt_exp (principal z)).comp z hp
  have ha := he.mul ((hasDerivAt_const z (1 : ℂ)).add hp)
  have hn : Complex.exp (principal z) * (1 + principal z) ≠ 0 := by
    rw [← deriv_mulExp]
    exact deriv_mulExp_ne_zero_of_mem_principalRange (principal_mem hz)
  have hd := ha.inv hn
  have hformula : deriv principal =ᶠ[𝓝 z]
      (fun y => (Complex.exp (principal y) * (1 + principal y))⁻¹) := by
    filter_upwards [isOpen_principalDomain.mem_nhds hz] with y hy
    exact deriv_principal hy
  convert hd.congr_of_eventuallyEq hformula using 1
  dsimp only [Function.comp_def, Pi.add_apply, Pi.mul_apply]
  have h1 := (mul_ne_zero_iff.mp hn).2
  field_simp [h1]
  ; ring

@[simp] theorem iteratedDeriv_principal_two_zero : iteratedDeriv 2 principal 0 = -2 := by
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    (hasDerivAt_deriv_principal zero_mem_principalDomain).deriv

@[simp] theorem iteratedDeriv_principal_three_zero : iteratedDeriv 3 principal 0 = 9 := by
  have hp : HasDerivAt principal 1 0 := by simpa using hasDerivAt_principal zero_mem_principalDomain
  have he : HasDerivAt (fun z => Complex.exp (principal z)) 1 0 := by
    simpa [Function.comp_def] using (Complex.hasDerivAt_exp (principal 0)).comp 0 hp
  have hn : HasDerivAt (fun z => -(Complex.exp (principal z) * (2 + principal z))) (-3) 0 := by
    convert (he.mul ((hasDerivAt_const (0 : ℂ) 2).add hp)).neg using 1; norm_num [Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
  have hd : HasDerivAt (fun z => (Complex.exp (principal z) * (1 + principal z)) ^ 3) 6 0 := by
    convert (he.mul ((hasDerivAt_const (0 : ℂ) 1).add hp)).pow 3 using 1; norm_num [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  have h : HasDerivAt (deriv (deriv principal)) 9 0 := by
    have hq := hn.div hd (by simp)
    have hformula : deriv (deriv principal) =ᶠ[𝓝 (0 : ℂ)]
        (fun z => -(Complex.exp (principal z) * (2 + principal z)) /
          (Complex.exp (principal z) * (1 + principal z)) ^ 3) := by
      filter_upwards [isOpen_principalDomain.mem_nhds zero_mem_principalDomain] with z hz
      exact (hasDerivAt_deriv_principal hz).deriv
    convert hq.congr_of_eventuallyEq hformula using 1; norm_num
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h.deriv

/-- The disk of radius `1/e` lies in the analytic slit domain. -/
theorem ball_zero_exp_neg_one_subset_principalDomain :
    Metric.ball (0 : ℂ) (Real.exp (-1)) ⊆ principalDomain := by
  intro z hz
  have hn : ‖z‖ < Real.exp (-1) := by simpa using hz
  exact Or.inr (lt_of_lt_of_le (neg_lt_neg hn) ((abs_le.mp (Complex.abs_re_le_norm z)).1))

/-- Convergence of the complete Taylor series, with derivative coefficients. -/
theorem hasSum_principal_taylor {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * iteratedDeriv n principal 0 * z ^ n)
      (principal z) := by
  have hd : DifferentiableOn ℂ principal (Metric.ball 0 (Real.exp (-1))) := by
    intro z hz
    exact (analyticAt_principal (ball_zero_exp_neg_one_subset_principalDomain hz)).differentiableAt.differentiableWithinAt
  convert Complex.hasSum_taylorSeries_on_ball hd (by simpa using hz) using 1
  funext n
  simp only [sub_zero, smul_eq_mul]
  ring

/-- `W(z) = z - z² + (3/2) z³ + z⁴ R(z)`, with `R` analytic near zero. -/
theorem exists_principal_cubic_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z in 𝓝 0,
      principal z = z - z ^ 2 + (3 / 2 : ℂ) * z ^ 3 + z ^ 4 * R z := by
  obtain ⟨R, hR, h⟩ := (analyticAt_principal zero_mem_principalDomain).exists_eventuallyEq_sum_add_pow_mul 4
  refine ⟨R, hR, ?_⟩
  filter_upwards [h] with z hz
  convert hz using 1
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul]
  ; ring

end LambertW.Complex
