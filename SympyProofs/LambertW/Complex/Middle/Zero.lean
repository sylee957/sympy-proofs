import SympyProofs.LambertW.Complex.Middle.Global
import SympyProofs.LambertW.Complex.Principal.Analytic

/-! # Divergence of the double-cut middle branch at zero -/
namespace LambertW.Complex
open Set Filter Topology

theorem middleDomain_subset_principalDomain : middleDomain ⊆ principalDomain := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr hz.1

/-- The two analytic inverses never coincide on the double-cut domain. -/
theorem middle_ne_principal {z : ℂ} (hz : z ∈ middleDomain) : middle z ≠ principal z := by
  intro he
  let : PreconnectedSpace middleDomain := Subtype.preconnectedSpace
    ((starConvex_middleDomain middleBase_mem).isPathConnected
      (ofReal_mem_middleDomain.mpr middleBase_mem)).isConnected.isPreconnected
  have hF : Continuous (fun t : middleDomain => middle t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticOnNhd_middle _ t.property).continuousAt.comp continuous_subtype_val.continuousAt)
  have hG : Continuous (fun t : middleDomain => principal t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticAt_principal (middleDomain_subset_principalDomain t.property)).continuousAt.comp
        continuous_subtype_val.continuousAt)
  have heq := eq_of_continuous_mulExp_lifts hF hG
    (fun t => (mulExp_middle t.property).trans
      (mulExp_principal (middleDomain_subset_principalDomain t.property)).symm)
    (fun t => by rw [mulExp_middle t.property]; exact middleDomain_ne_criticalValue t.property)
    (t₀ := ⟨z, hz⟩) he
  have hb := congrFun heq ⟨(middleBase : ℂ), ofReal_mem_middleDomain.mpr middleBase_mem⟩
  change middle (middleBase : ℂ) = principal (middleBase : ℂ) at hb
  rw [middle_ofReal middleBase_mem, principal_ofReal middleBase_mem.1] at hb
  have hh := Complex.ofReal_injective hb
  have hl := Real.lower_lt_neg_one middleBase_mem
  have hp := Real.principal_mem (le_of_lt middleBase_mem.1)
  change -1 ≤ Real.principal middleBase at hp
  linarith

theorem middle_not_mem_principalRange {z : ℂ} (hz : z ∈ middleDomain) :
    middle z ∉ principalRange := by
  intro hw
  exact middle_ne_principal hz (eq_principal_of_mulExp_eq hw (mulExp_middle hz))

/-- The entire middle branch stays a fixed positive distance away from zero. -/
theorem exists_pos_le_norm_middle :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ middleDomain, r ≤ ‖middle z‖ := by
  have hzero : (0 : ℂ) ∈ principalRange := by
    simpa only [principal_zero] using principal_mem zero_mem_principalDomain
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_principalRange 0 hzero
  refine ⟨r, hr, fun z hz => ?_⟩
  by_contra hn
  exact middle_not_mem_principalRange hz (hball (by simpa using lt_of_not_ge hn))

/-- Complex divergence at zero, along arbitrary approaches in the double-cut domain. -/
theorem tendsto_norm_middle_zero :
    Tendsto (fun z => ‖middle z‖) (𝓝[middleDomain] 0) atTop := by
  obtain ⟨r, hr, hbound⟩ := exists_pos_le_norm_middle
  apply tendsto_atTop.2
  intro M
  have hepos : 0 < r * Real.exp (-M) := mul_pos hr (Real.exp_pos _)
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[middleDomain] 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have ht : ∀ᶠ z : ℂ in 𝓝[middleDomain] 0, ‖z‖ < r * Real.exp (-M) :=
    hnorm.eventually (eventually_lt_nhds hepos)
  filter_upwards [self_mem_nhdsWithin, ht] with z hz hsmall
  by_contra hn
  have hw : ‖middle z‖ < M := lt_of_not_ge hn
  have hre : -M ≤ (middle z).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (middle z))).1
    linarith
  have hmul : r * Real.exp (-M) ≤ ‖middle z‖ * Real.exp (middle z).re :=
    mul_le_mul (hbound z hz) (Real.exp_le_exp.mpr hre) (le_of_lt (Real.exp_pos _))
      (norm_nonneg _)
  have he : ‖z‖ = ‖middle z‖ * Real.exp (middle z).re := by
    simpa only [mulExp, norm_mul, Complex.norm_exp] using
      (congrArg norm (mulExp_middle hz)).symm
  linarith

/-- On negative real inputs the divergence is specifically toward `-∞`. -/
theorem tendsto_re_middle_nhdsLT_zero :
    Tendsto (fun x : ℝ => (middle (x : ℂ)).re) (𝓝[<] 0) atBot := by
  apply Real.tendsto_lower_nhdsLT_zero.congr'
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hxlo
  simp [middle_ofReal ⟨hxlo, hx⟩]

/-- A branch-independent logarithmic identity, using real logarithms of norms. -/
theorem re_middle_eq_log_norm {z : ℂ} (hz : z ∈ middleDomain) :
    (middle z).re = Real.log ‖z‖ - Real.log ‖middle z‖ := by
  have hn : middle z ≠ 0 := by
    intro he
    have hh := mulExp_middle hz
    rw [he, mulExp_zero] at hh
    exact middleDomain_ne_zero hz hh.symm
  have hh := congrArg (fun w : ℂ => Real.log ‖w‖) (mulExp_middle hz)
  simp only [mulExp, norm_mul, Complex.norm_exp] at hh
  rw [Real.log_mul (norm_ne_zero_iff.mpr hn) (Real.exp_ne_zero _), Real.log_exp] at hh
  linarith

/-- The real part tends to `-∞` along every complex approach in the domain. -/
theorem tendsto_re_middle_zero :
    Tendsto (fun z => (middle z).re) (𝓝[middleDomain] 0) atBot := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[middleDomain] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.mpr (middleDomain_ne_zero hz)
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hnorm
  apply tendsto_atBot.2
  intro M
  filter_upwards [(tendsto_atBot.1 hlog) M,
    (tendsto_atTop.1 tendsto_norm_middle_zero) 1, self_mem_nhdsWithin] with z hz hn hd
  rw [re_middle_eq_log_norm hd]
  have hh := Real.log_nonneg hn
  dsimp only [Function.comp_def] at hz
  linarith

/-- The logarithmic correction itself diverges negatively. No complex-log
branch convention is needed for this identity and limit. -/
theorem tendsto_re_middle_sub_log_norm_zero :
    Tendsto (fun z => (middle z).re - Real.log ‖z‖) (𝓝[middleDomain] 0) atBot := by
  have ht := tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp tendsto_norm_middle_zero)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp only [Function.comp_def]
  rw [re_middle_eq_log_norm hz]
  ring

/-- Leading logarithmic asymptotic on the negative real axis:
`Re (middle x) / log (-x) → 1`. -/
theorem tendsto_re_middle_div_log_neg :
    Tendsto (fun x : ℝ => (middle (x : ℂ)).re / Real.log (-x)) (𝓝[<] 0) (𝓝 1) := by
  have ht := tendsto_neg_atBot_atTop.comp Real.tendsto_lower_nhdsLT_zero
  have hsmall : Tendsto (fun x : ℝ => Real.log (-Real.lower x) / (-Real.lower x))
      (𝓝[<] 0) (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hratio : Tendsto (fun x : ℝ => 1 - Real.log (-Real.lower x) / (-Real.lower x))
      (𝓝[<] 0) (𝓝 1) := by simpa using tendsto_const_nhds.sub hsmall
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  rw [inv_one] at hinv
  apply hinv.congr'
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hxlo
  change x < 0 at hx
  have hd : x ∈ Ioo (-Real.exp (-1)) 0 := ⟨hxlo, hx⟩
  have hw : Real.lower x < -1 := Real.lower_lt_neg_one hd
  have hlog := re_middle_eq_log_norm (ofReal_mem_middleDomain.mpr hd)
  rw [middle_ofReal hd] at hlog ⊢
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg hx, abs_of_neg (by linarith : Real.lower x < 0)] at hlog
  simp only [Complex.ofReal_re]
  have hn : Real.lower x ≠ 0 := by linarith
  have hln : Real.log (-x) = Real.lower x + Real.log (-Real.lower x) := by linarith
  rw [hln]
  field_simp
  ring

end LambertW.Complex
