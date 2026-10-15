import SympyProofs.LambertW.Complex.Boundary.Side
import SympyProofs.LambertW.Complex.Boundary.Internal.MinusOne.Upper
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lower-side range bounds, endpoints, and the singularity at zero -/
namespace LambertW.Complex
open Set Filter Topology

/-- Real points are approachable from the lower half-plane. -/
theorem nhdsWithin_lower_neBot (x : ℝ) :
    NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) :=
  BoundarySide.nhdsWithin_halfPlane_neBot .lower x

/-- The lower-half-plane sheet stays strictly below imaginary part `-π`. -/
theorem im_minusOne_lt_neg_pi {z : ℂ} (hz : z.im < 0) :
    ((branch (-1)) z).im < -Real.pi := by
  have hc : ContinuousAt (fun z => ((branch (-1)) z).im) ((branchRadius 0 : ℝ) : ℂ) :=
    Complex.continuous_im.continuousAt.comp
      ((analyticOnNhd_branch (-1)) _ (negativeBranchSeed 0).mem_domain).continuousAt
  have hb : ((branch (-1)) ((branchRadius 0 : ℝ) : ℂ)).im < -Real.pi := by
    rw [(show branch (-1) (branchRadius 0) = negativeBranchValue 0 from branch_negSucc_base 0)]
    simp [negativeBranchValue, branchRadius, Complex.mul_im]
    linarith [Real.pi_pos]
  have hev := (hc.tendsto.eventually (eventually_lt_nhds hb)).filter_mono
    (show 𝓝[{z : ℂ | z.im < 0}] ((branchRadius 0 : ℝ) : ℂ) ≤ 𝓝 ((branchRadius 0 : ℝ) : ℂ) from nhdsWithin_le_nhds)
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] ((branchRadius 0 : ℝ) : ℂ)) :=
    nhdsWithin_lower_neBot (branchRadius 0)
  have hex : ∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] ((branchRadius 0 : ℝ) : ℂ),
      z.im < 0 ∧ ((branch (-1)) z).im < -Real.pi := by
    filter_upwards [self_mem_nhdsWithin, hev] with z hz hv
    exact ⟨hz, hv⟩
  obtain ⟨a, ha, hav⟩ := hex.exists
  by_contra hle
  have hcont : ContinuousOn (fun z => ((branch (-1)) z).im) {z : ℂ | z.im < 0} := by
    intro y hy
    exact (Complex.continuous_im.continuousAt.comp
      ((analyticOnNhd_branch (-1)) _ (Or.inr (ne_of_lt hy))).continuousAt).continuousWithinAt
  obtain ⟨y, hy, he⟩ := (convex_halfSpace_im_lt 0).isPreconnected.intermediate_value
    ha hz hcont ⟨hav.le, le_of_not_gt hle⟩
  have hi := congrArg Complex.im ((mulExp_branch (-1)) (Or.inr (ne_of_lt hy)))
  dsimp only at he
  rw [mulExp_im, he] at hi
  simp only [Real.sin_neg, Real.sin_pi, neg_zero, mul_zero, Real.cos_neg, Real.cos_pi,
    mul_neg_one, neg_neg, zero_add] at hi
  change y.im < 0 at hy
  have hp : 0 < Real.exp ((branch (-1)) y).re * Real.pi := mul_pos (Real.exp_pos _) Real.pi_pos
  linarith

theorem neg_two_pi_lt_im_minusOne_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    -(2 * Real.pi) < ((branch (-1)) z).im := by
  have hc : ContinuousAt (fun z => ((branch (-1)) z).im) ((branchRadius 0 : ℝ) : ℂ) :=
    Complex.continuous_im.continuousAt.comp
      ((analyticOnNhd_branch (-1)) _ (negativeBranchSeed 0).mem_domain).continuousAt
  have hb : -(2 * Real.pi) < ((branch (-1)) ((branchRadius 0 : ℝ) : ℂ)).im := by
    rw [(show branch (-1) (branchRadius 0) = negativeBranchValue 0 from branch_negSucc_base 0)]
    simp [negativeBranchValue, branchRadius, Complex.mul_im]
    linarith [Real.pi_pos]
  have hev := (hc.tendsto.eventually (eventually_gt_nhds hb)).filter_mono
    (show 𝓝[{z : ℂ | 0 < z.im}] ((branchRadius 0 : ℝ) : ℂ) ≤ 𝓝 ((branchRadius 0 : ℝ) : ℂ) from nhdsWithin_le_nhds)
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] ((branchRadius 0 : ℝ) : ℂ)) :=
    nhdsWithin_upper_neBot (branchRadius 0)
  have hex : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] ((branchRadius 0 : ℝ) : ℂ),
      0 < z.im ∧ -(2 * Real.pi) < ((branch (-1)) z).im := by
    filter_upwards [self_mem_nhdsWithin, hev] with z hz hv
    exact ⟨hz, hv⟩
  obtain ⟨a, ha, hav⟩ := hex.exists
  by_contra hle
  have hcont : ContinuousOn (fun z => ((branch (-1)) z).im) {z : ℂ | 0 < z.im} := by
    intro y hy
    exact (Complex.continuous_im.continuousAt.comp
      ((analyticOnNhd_branch (-1)) _ (Or.inr (ne_of_gt hy))).continuousAt).continuousWithinAt
  obtain ⟨y, hy, he⟩ := (convex_halfSpace_im_gt 0).isPreconnected.intermediate_value
    hz ha hcont ⟨le_of_not_gt hle, hav.le⟩
  have hi := congrArg Complex.im ((mulExp_branch (-1)) (Or.inr (ne_of_gt hy)))
  dsimp only at he
  rw [mulExp_im, he] at hi
  simp only [Real.sin_neg, Real.sin_two_pi, neg_zero, mul_zero, Real.cos_neg,
    Real.cos_two_pi, mul_one, zero_add] at hi
  change 0 < y.im at hy
  have hp : Real.exp ((branch (-1)) y).re * -(2 * Real.pi) < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith [Real.pi_pos])
  linarith

/-- A uniform lower bound on the norm in the lower half-plane. -/
theorem two_le_norm_minusOne_of_im_neg {z : ℂ} (hz : z.im < 0) : 2 ≤ ‖(branch (-1)) z‖ := by
  have hi := im_minusOne_lt_neg_pi hz
  have hn := Complex.abs_im_le_norm ((branch (-1)) z)
  rw [abs_of_neg (by linarith [Real.pi_pos])] at hn
  linarith [Real.pi_gt_three]

/-- Uniform inverse-derivative bound on the lower sheet away from zero. -/
theorem norm_deriv_minusOne_le_of_im_neg {z : ℂ} {δ : ℝ}
    (hz : z.im < 0) (hδ : 0 < δ) (hbound : δ ≤ ‖z‖) :
    ‖deriv (branch (-1)) z‖ ≤ 2 / δ := by
  rw [(deriv_branch (-1)) (Or.inr (ne_of_lt hz))]
  exact norm_inverse_derivative_le_of_norm_ge hδ hbound
    (two_le_norm_minusOne_of_im_neg hz) ((mulExp_branch (-1)) (Or.inr (ne_of_lt hz)))

/-- The lower-side limit exists even at the critical input `-1/e`:
this sheet stays away from the critical inverse value `-1`. -/
theorem exists_minusOne_lower_limit_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∃ w : ℂ, Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  let δ : ℝ := ‖(x : ℂ)‖ / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (norm_pos_iff.mpr (by exact_mod_cast hx))
  let S : Set ℂ := {z : ℂ | z.im < 0} ∩ Metric.ball (x : ℂ) δ
  have hnorm : ∀ z ∈ S, δ ≤ ‖z‖ := by
    intro z hz
    have hh := norm_sub_le ((x : ℂ) - z) (-z)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    have hd : ‖(x : ℂ) - z‖ < δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
    dsimp [δ] at *
    linarith
  let C : NNReal := ⟨2 / δ, le_of_lt (div_pos (by norm_num) hδ)⟩
  have hLip : LipschitzOnWith C (branch (-1)) S := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => ((analyticOnNhd_branch (-1)) _ (Or.inr (ne_of_lt hz.1))).differentiableAt)
    · intro z hz
      exact norm_deriv_minusOne_le_of_im_neg hz.1 hδ (hnorm z hz)
    · exact (convex_halfSpace_im_lt 0).inter (convex_ball _ _)
  apply cauchy_map_iff_exists_tendsto.mp
  have hc : Cauchy (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) :=
    cauchy_nhds.mono nhdsWithin_le_nhds
  apply hc.map_of_le hLip.uniformContinuousOn
  apply Filter.le_principal_iff.mpr
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ z in 𝓝 (x : ℂ), z ∈ Metric.ball (x : ℂ) δ from
      Metric.ball_mem_nhds (x : ℂ) hδ).filter_mono nhdsWithin_le_nhds] with z hz hb
  exact ⟨hz, hb⟩

/-- Every finite lower boundary value lies below `-π`, hence cannot be `-1`. -/
theorem im_minusOne_lower_limit_le_neg_pi {x : ℝ} {w : ℂ}
    (hw : Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w)) :
    w.im ≤ -Real.pi := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  apply le_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hw)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (im_minusOne_lt_neg_pi hz).le

/-- Divergence at zero from below on the indexed sheet. -/
theorem tendsto_norm_minusOne_lower_zero :
    Tendsto (fun z => ‖(branch (-1)) z‖) (𝓝[{z : ℂ | z.im < 0}] 0) atTop := by
  apply tendsto_atTop.2
  intro M
  have hp : 0 < 2 * Real.exp (-M) := by positivity
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[{z : ℂ | z.im < 0}] 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnorm.eventually (eventually_lt_nhds hp)] with z hz hs
  by_contra hn
  have hM : ‖(branch (-1)) z‖ < M := lt_of_not_ge hn
  have hr : -M ≤ ((branch (-1)) z).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm ((branch (-1)) z))).1
    linarith
  have hb := mul_le_mul (two_le_norm_minusOne_of_im_neg hz) (Real.exp_le_exp.mpr hr)
    (le_of_lt (Real.exp_pos (-M))) (norm_nonneg ((branch (-1)) z))
  have he : ‖z‖ = ‖(branch (-1)) z‖ * Real.exp ((branch (-1)) z).re := by
    simpa only [mulExp, norm_mul, Complex.norm_exp] using
      (congrArg norm ((mulExp_branch (-1)) (Or.inr (ne_of_lt hz)))).symm
  linarith

theorem existsUnique_minusOne_lower_limit_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∃! w : ℂ, Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  obtain ⟨w, hw⟩ := exists_minusOne_lower_limit_of_ne_zero hx
  exact ⟨w, hw, fun v hv => tendsto_nhds_unique hv hw⟩

/-- Upper limits at negative real inputs have imaginary part strictly above `-π`. -/
theorem neg_pi_lt_im_minusOne_upper_limit {x : ℝ} (hx : x < 0) {w : ℂ}
    (hw : Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w))
    (hi : mulExp w = (x : ℂ)) : -Real.pi < w.im := by
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := nhdsWithin_upper_neBot x
  have hlo : -(2 * Real.pi) ≤ w.im := by
    apply ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hw)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (neg_two_pi_lt_im_minusOne_of_im_pos hz).le
  by_contra hn
  have hhi : w.im ≤ -Real.pi := le_of_not_gt hn
  have hs : 0 ≤ Real.sin w.im := by
    have hh := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ w.im + 2 * Real.pi by linarith)
      (show w.im + 2 * Real.pi ≤ Real.pi by linarith)
    simpa using hh
  have hr := congrArg Complex.re hi
  have hm := congrArg Complex.im hi
  rw [mulExp_re, Complex.ofReal_re] at hr
  rw [mulExp_im, Complex.ofReal_im] at hm
  have he : x * Real.sin w.im = -Real.exp w.re * w.im := by
    linear_combination -Real.sin w.im * hr + Real.cos w.im * hm -
      Real.exp w.re * w.im * (Real.sin_sq_add_cos_sq w.im)
  have hleft : x * Real.sin w.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx.le hs
  have hright : 0 < -Real.exp w.re * w.im :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos (Real.exp_pos _)) (by linarith [Real.pi_pos])
  linarith

/-- The real part also tends to `-∞` as the input tends to zero from below. -/
theorem tendsto_re_minusOne_lower_zero :
    Tendsto (fun z => ((branch (-1)) z).re) (𝓝[{z : ℂ | z.im < 0}] 0) atBot := by
  apply tendsto_atBot.2
  intro M
  have hp : 0 < 2 * Real.exp M := by positivity
  have ht : Tendsto (fun z : ℂ => ‖z‖) (𝓝[{z : ℂ | z.im < 0}] 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, ht.eventually (eventually_lt_nhds hp)] with z hz hs
  by_contra hn
  have hr : M ≤ ((branch (-1)) z).re := (lt_of_not_ge hn).le
  have hb := mul_le_mul (two_le_norm_minusOne_of_im_neg hz) (Real.exp_le_exp.mpr hr)
    (le_of_lt (Real.exp_pos M)) (norm_nonneg ((branch (-1)) z))
  have he : ‖z‖ = ‖(branch (-1)) z‖ * Real.exp ((branch (-1)) z).re := by
    simpa only [mulExp, norm_mul, Complex.norm_exp] using
      (congrArg norm ((mulExp_branch (-1)) (Or.inr (ne_of_lt hz)))).symm
  linarith

end LambertW.Complex
