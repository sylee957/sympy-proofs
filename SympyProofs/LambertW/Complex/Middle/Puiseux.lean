import SympyProofs.LambertW.Complex.Middle.BranchPoint
import SympyProofs.LambertW.Complex.Principal.PuiseuxRecurrence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The negative square-root parameter for the middle branch -/

namespace LambertW.Complex

open Set Filter Topology

private theorem middle_displacement_tendsto :
    Tendsto (fun x : ℝ => ((Real.lower x + 1 : ℝ) : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (Real.tendsto_lower_nhdsGT_branchPoint.add_const 1)
  simpa [Function.comp_def] using h

/-- The normalized coordinate selects exactly the negative real square root. -/
theorem eventually_middle_puiseux_parameter {P : ℂ → ℂ}
    (hP0 : P 0 = 0) (hdP : HasDerivAt P 1 0)
    (hsq : ∀ u, P u ^ 2 = branchSeries u) :
    ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
      P ((Real.lower x + 1 : ℝ) : ℂ) =
        ((-Real.sqrt (2 * Real.exp 1 * (x + Real.exp (-1))) : ℝ) : ℂ) := by
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  have hdom : ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)), x ∈ Ioo (-Real.exp (-1)) 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hx0
    exact ⟨hx, hx0⟩
  have hu : Tendsto (fun x : ℝ => ((Real.lower x + 1 : ℝ) : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨middle_displacement_tendsto, ?_⟩
    filter_upwards [hdom] with x hx
    change ((Real.lower x + 1 : ℝ) : ℂ) ≠ 0
    have hl := Real.lower_lt_neg_one hx
    exact_mod_cast (show Real.lower x + 1 ≠ 0 by linarith)
  have ht : Tendsto (fun x : ℝ => P ((Real.lower x + 1 : ℝ) : ℂ) /
      ((Real.lower x + 1 : ℝ) : ℂ)) (𝓝[>] (-Real.exp (-1))) (𝓝 1) := by
    simpa [Function.comp_def, slope, hP0, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_iff_tendsto_slope.mp hdP).comp hu
  have hr := (Complex.continuous_re.tendsto 1).comp ht
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
      0 < (P ((Real.lower x + 1 : ℝ) : ℂ) / ((Real.lower x + 1 : ℝ) : ℂ)).re :=
    hr.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))
  filter_upwards [hdom, hpos] with x hx hp
  let s : ℝ := Real.sqrt (2 * Real.exp 1 * (x + Real.exp (-1)))
  have hxpos : 0 ≤ x + Real.exp (-1) := by linarith [hx.1]
  have hs : s ^ 2 = 2 * Real.exp 1 * (x + Real.exp (-1)) :=
    Real.sq_sqrt (by positivity)
  have he : P ((Real.lower x + 1 : ℝ) : ℂ) ^ 2 = (s : ℂ) ^ 2 := by
    rw [hsq, branchSeries_eq]
    have hw : ((Real.lower x + 1 : ℝ) : ℂ) - 1 = (Real.lower x : ℂ) := by push_cast; ring
    rw [hw, mulExp_ofReal, Real.mulExp_lower ⟨hx.1.le, hx.2⟩, mulExp_neg_one]
    rw [← Complex.ofReal_pow, hs]
    push_cast
    simp only [sub_neg_eq_add]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
  · rw [he, ← Complex.ofReal_div, Complex.ofReal_re] at hp
    have hn : Real.lower x + 1 < 0 := by have := Real.lower_lt_neg_one hx; linarith
    have hh : s / (Real.lower x + 1) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hn.le
    exact False.elim (not_lt_of_ge hh hp)
  · simpa only [Complex.ofReal_neg] using he

/-- Near the real branch point, the middle branch is the analytic Puiseux inverse
at the negative square root. Its full rational-coefficient series converges,
and its cubic truncation has an analytic fourth-order remainder. -/
theorem exists_middle_puiseux_expansion :
    ∃ Q R : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
      Q 0 = 0 ∧ HasDerivAt Q 1 0 ∧
      ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
        let p : ℂ := ((-Real.sqrt (2 * Real.exp 1 * (x + Real.exp (-1))) : ℝ) : ℂ)
        (Real.lower x : ℂ) = -1 + Q p ∧
        HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * p ^ n) ((Real.lower x : ℂ) + 1) ∧
        (Real.lower x : ℂ) = -1 + p - p ^ 2 / 3 +
          (11 / 72 : ℂ) * p ^ 3 + p ^ 4 * R p := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, hsq, hleft, hright⟩ :=
    exists_puiseux_coordinates
  have he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 := by
    filter_upwards [hright] with p hp
    rw [← hsq, hp]
  obtain ⟨R, hR, hseries⟩ := puiseux_inverse_cubic_remainder hQ hQ0 hdQ he
  obtain ⟨r, hr, hsum⟩ := exists_pos_hasSum_puiseuxCoeff hQ hQ0 hdQ he
  have hp : Tendsto (fun x : ℝ => P ((Real.lower x + 1 : ℝ) : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝 0) := by
    simpa only [Function.comp_def, hP0] using
      hP.continuousAt.tendsto.comp middle_displacement_tendsto
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
      ‖P ((Real.lower x + 1 : ℝ) : ℂ)‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hp.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)
  refine ⟨Q, R, hQ, hR, hQ0, hdQ, ?_⟩
  filter_upwards [eventually_middle_puiseux_parameter hP0 hdP hsq,
    middle_displacement_tendsto.eventually hleft, hp.eventually hseries, hsmall]
    with x hparam hvalue hcubic hnorm
  rw [hparam] at hvalue hcubic hnorm
  dsimp only
  have hv : Q (((-Real.sqrt (2 * Real.exp 1 * (x + Real.exp (-1))) : ℝ) : ℂ)) =
      (Real.lower x : ℂ) + 1 := by simpa using hvalue
  refine ⟨by linear_combination -hv, ?_, ?_⟩
  · simpa only [hv] using hsum _ hnorm
  · rw [hv] at hcubic
    linear_combination hcubic

end LambertW.Complex
