import SympyProofs.LambertW.Complex.Middle.Puiseux

/-! # Analytic middle inverse on a slit neighborhood of the branch point

The parameter uses the principal complex square root with a minus sign.
The construction is local at the branch point, not a global indexed branch.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- The negative square-root coordinate on the slit plane based at `-1/e`. -/
noncomputable def middleParameter (z : ℂ) : ℂ :=
  -Complex.sqrt (2 * Complex.exp 1 * (z + Complex.exp (-1)))

theorem middleParameter_sq (z : ℂ) :
    middleParameter z ^ 2 = 2 * Complex.exp 1 * (z + Complex.exp (-1)) := by
  simp only [middleParameter, neg_sq, Complex.sqrt]
  rw [Complex.cpow_ofNat_inv_pow]

/-- The slit-domain condition ensures analyticity of the square-root coordinate. -/
theorem analyticAt_middleParameter {z : ℂ}
    (hz : 2 * Complex.exp 1 * (z + Complex.exp (-1)) ∈ Complex.slitPlane) :
    AnalyticAt ℂ middleParameter z := by
  have hs : AnalyticAt ℂ Complex.sqrt (2 * Complex.exp 1 * (z + Complex.exp (-1))) := Complex.differentiableOn_sqrt.analyticAt
    (Complex.isOpen_slitPlane.mem_nhds hz)
  have hf : AnalyticAt ℂ (fun z : ℂ => 2 * Complex.exp 1 * (z + Complex.exp (-1))) z := by fun_prop
  exact (hs.comp (f := fun z : ℂ => 2 * Complex.exp 1 * (z + Complex.exp (-1))) (x := z) hf).neg

theorem middleParameter_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    middleParameter (x : ℂ) =
      ((-Real.sqrt (2 * Real.exp 1 * (x + Real.exp (-1))) : ℝ) : ℂ) := by
  have hn : 0 ≤ 2 * Real.exp 1 * (x + Real.exp (-1)) := by
    have : 0 ≤ x + Real.exp (-1) := by linarith
    positivity
  have hc : ((2 * Real.exp 1 * (x + Real.exp (-1)) : ℝ) : ℂ) =
      2 * Complex.exp 1 * ((x : ℂ) + Complex.exp (-1)) := by push_cast; rfl
  rw [middleParameter, ← hc, Complex.sqrt]
  have hh := Complex.ofReal_cpow hn (1 / 2 : ℝ)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, one_div] at hh
  simp only [one_div] at hh
  rw [← hh]
  simp [Real.sqrt_eq_rpow]

/-- An analytic inverse on a slit neighborhood, agreeing with the real lower
branch near the branch point. The radius is measured in the square-root parameter. -/
theorem exists_analytic_middle_slit :
    ∃ Q : ℂ → ℂ, ∃ r : ℝ, 0 < r ∧ AnalyticAt ℂ Q 0 ∧
      (∀ z : ℂ, 2 * Complex.exp 1 * (z + Complex.exp (-1)) ∈ Complex.slitPlane →
        ‖middleParameter z‖ < r →
        AnalyticAt ℂ (fun z => -1 + Q (middleParameter z)) z ∧
        mulExp (-1 + Q (middleParameter z)) = z) ∧
      (∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
        -1 + Q (middleParameter (x : ℂ)) = (Real.lower x : ℂ)) ∧
      Q 0 = 0 ∧ HasDerivAt Q 1 0 ∧ (∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2) := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hdP, hdQ, hsq, hleft, hright⟩ :=
    exists_puiseux_coordinates
  have he : ∀ᶠ p in 𝓝 0, branchSeries (Q p) = p ^ 2 := by
    filter_upwards [hright] with p hp
    rw [← hsq, hp]
  obtain ⟨a, ha, hball⟩ := hQ.exists_ball_analyticOnNhd
  obtain ⟨b, hb, hbball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨Q, min a b, lt_min ha hb, hQ, ?_, ?_⟩
  · intro z hz hr
    have hqa := hball (middleParameter z) (by simpa using (lt_min_iff.mp hr).1)
    refine ⟨analyticAt_const.add (hqa.comp (analyticAt_middleParameter hz)), ?_⟩
    have hi := hbball (show middleParameter z ∈ Metric.ball 0 b by
      simpa using (lt_min_iff.mp hr).2)
    change branchSeries (Q (middleParameter z)) = middleParameter z ^ 2 at hi
    rw [branchSeries_eq, middleParameter_sq, mulExp_neg_one] at hi
    have hn : (2 : ℂ) * Complex.exp 1 ≠ 0 := mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
    have hh := (mul_left_cancel₀ hn hi)
    have heq : -1 + Q (middleParameter z) = Q (middleParameter z) - 1 := by ring
    rw [heq]
    linear_combination hh
  · refine ⟨?_, hQ0, hdQ, he⟩
    have hw : Tendsto (fun x : ℝ => ((Real.lower x + 1 : ℝ) : ℂ))
        (𝓝[>] (-Real.exp (-1))) (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp
        (Real.tendsto_lower_nhdsGT_branchPoint.add_const 1)
    filter_upwards [eventually_middle_puiseux_parameter hP0 hdP hsq,
      hw.eventually hleft, self_mem_nhdsWithin] with x hp hq hx
    rw [hp] at hq
    rw [middleParameter_ofReal (le_of_lt (show -Real.exp (-1) < x from hx))]
    simp only [Complex.ofReal_add, Complex.ofReal_one] at hq
    linear_combination hq

end LambertW.Complex
