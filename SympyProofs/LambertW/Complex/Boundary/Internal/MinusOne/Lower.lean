import SympyProofs.LambertW.Complex.Boundary.Internal.MinusOne.LowerEndpoint

/-! # Lower-side boundary values of indexed W₋₁

These are constructed directly from the indexed branch, independently of the
middle branch. Lower-side limits and assignments cover every nonzero real input,
including `-1/e`, where this sheet has a noncritical inverse value.
-/
namespace LambertW.Complex
open Set Filter Topology

theorem exists_minusOne_lower_extension {x : ℝ} (hx0 : x ≠ 0)
    (hxb : x ≠ -Real.exp (-1)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧ mulExp (F x) = x ∧
      ∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] (x : ℂ), (branch (-1)) z = F z := by
  let H : Set ℂ := {z | z.im < 0}
  have hH : IsOpen H := isOpen_lt Complex.continuous_im continuous_const
  have hconv : Convex ℝ H := by
    intro a ha b hb s t hs ht hst
    change (s • a + t • b).im < 0
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    change a.im < 0 at ha
    change b.im < 0 at hb
    by_cases hs0 : s = 0
    · have ht1 : t = 1 := by linarith
      simpa [hs0, ht1] using hb
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      nlinarith [mul_neg_of_pos_of_neg hsp ha, mul_nonpos_of_nonneg_of_nonpos ht (le_of_lt hb)]
  have hxc : (x : ℂ) ≠ -Complex.exp (-1) := by
    intro he
    apply hxb
    have hh := congrArg Complex.re he
    simpa [Complex.exp_re] using hh
  have ho : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ -Complex.exp (-1)} := isOpen_ne.inter isOpen_ne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho (x : ℂ)
    ⟨by exact_mod_cast hx0, hxc⟩
  let c : ℂ := (x : ℂ) + (-(r / 2) : ℝ) * Complex.I
  have hcH : c ∈ H := by change c.im < 0; simp [c]; linarith
  have hcb : c ∈ Metric.ball (x : ℂ) r := by
    simp only [Metric.mem_ball, dist_eq_norm, c, add_sub_cancel_left, norm_mul,
      Complex.norm_real, norm_neg, Complex.norm_I, mul_one]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  let U := H ∪ Metric.ball (x : ℂ) r
  have hc : c ∈ U := Or.inl hcH
  have hstar : StarConvex ℝ c U :=
    (hconv.starConvex hcH).union ((convex_ball _ _).starConvex hcb)
  have hregular : ∀ z ∈ U, z ≠ 0 ∧ z ≠ -Complex.exp (-1) := by
    intro z hz
    rcases hz with hz | hz
    · constructor
      · intro he; simp [he, H] at hz
      · intro he; simp [he, H, Complex.exp_im] at hz
    · exact hball hz
  have hcD : c ∈ branchDomain := Or.inr (ne_of_lt hcH)
  obtain ⟨F, hF, hFc, hFi⟩ := exists_analytic_inverse_on_starDomain
    (hH.union Metric.isOpen_ball) hstar hc (fun z hz => (hregular z hz).1)
    (fun z hz => (hregular z hz).2) ((mulExp_branch (-1)) hcD)
  have heq : EqOn (branch (-1)) F H := by
    let : PreconnectedSpace H := Subtype.preconnectedSpace hconv.isPreconnected
    have hL : Continuous (fun t : H => (branch (-1)) t) :=
      continuous_iff_continuousAt.mpr (fun t =>
        ((analyticOnNhd_branch (-1)) _ (Or.inr (ne_of_lt t.property))).continuousAt.comp
          continuous_subtype_val.continuousAt)
    have hFc' : Continuous (fun t : H => F t) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (hF _ (Or.inl t.property)).continuousAt.comp continuous_subtype_val.continuousAt)
    have hh := eq_of_continuous_mulExp_lifts hL hFc'
      (fun t => ((mulExp_branch (-1)) (Or.inr (ne_of_lt t.property))).trans
        (hFi _ (Or.inl t.property)).symm)
      (fun t => by
        rw [(mulExp_branch (-1)) (Or.inr (ne_of_lt t.property))]
        exact (hregular t (Or.inl t.property)).2)
      (t₀ := ⟨c, hcH⟩) hFc.symm
    intro z hz
    exact congrFun hh ⟨z, hz⟩
  have hxU : (x : ℂ) ∈ U := Or.inr (Metric.mem_ball_self hr)
  refine ⟨F, hF _ hxU, hFi _ hxU, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact heq hz

/-- Finite lower-side limits exist at every regular real point. -/
theorem exists_minusOne_lower_limit {x : ℝ} (hx0 : x ≠ 0)
    (hxb : x ≠ -Real.exp (-1)) :
    ∃ w : ℂ, mulExp w = x ∧
      Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w) := by
  obtain ⟨F, hF, hi, he⟩ := exists_minusOne_lower_extension hx0 hxb
  refine ⟨F x, hi, ?_⟩
  apply (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [he] with z hz
  exact hz.symm


/-- The lower boundary limit at a regular real input is unique. -/
theorem existsUnique_minusOne_lower_limit {x : ℝ} (hx0 : x ≠ 0)
    (hxb : x ≠ -Real.exp (-1)) :
    ∃! w : ℂ, Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  obtain ⟨w, _, hw⟩ := exists_minusOne_lower_limit hx0 hxb
  exact ⟨w, hw, fun v hv => tendsto_nhds_unique hv hw⟩

/-- Lower boundary values at every nonzero real input, including `-1/e`.
The value at zero is unspecified. -/
noncomputable def minusOneLowerBoundary (x : ℝ) : ℂ :=
  if h : x ≠ 0 then
    (existsUnique_minusOne_lower_limit_of_ne_zero h).exists.choose else (branch (-1)) x

theorem tendsto_minusOne_lower_boundary {x : ℝ} (hx0 : x ≠ 0)
    :
    Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (minusOneLowerBoundary x)) := by
  simpa [minusOneLowerBoundary, hx0] using
    (existsUnique_minusOne_lower_limit_of_ne_zero hx0).exists.choose_spec

theorem minusOneLowerBoundary_eq_of_tendsto {x : ℝ} (hx0 : x ≠ 0)
    {w : ℂ}
    (hw : Tendsto (branch (-1)) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 w)) :
    minusOneLowerBoundary x = w := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  exact tendsto_nhds_unique (tendsto_minusOne_lower_boundary hx0) hw

theorem mulExp_minusOneLowerBoundary {x : ℝ} (hx0 : x ≠ 0)
    : mulExp (minusOneLowerBoundary x) = (x : ℂ) := by
  let : NeBot (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := nhdsWithin_lower_neBot x
  have ht := (analyticAt_mulExp _).continuousAt.tendsto.comp
    (tendsto_minusOne_lower_boundary hx0)
  apply tendsto_nhds_unique ht
  apply (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ((mulExp_branch (-1)) (Or.inr (ne_of_lt hz))).symm

/-- Positive real inputs are interior points of the indexed domain, so their
lower-side limits equal the already-defined analytic values. -/
theorem minusOneLowerBoundary_of_pos {x : ℝ} (hx : 0 < x) :
    minusOneLowerBoundary x = (branch (-1)) (x : ℂ) := by
  apply minusOneLowerBoundary_eq_of_tendsto (ne_of_gt hx)
  exact ((analyticOnNhd_branch (-1)) _ (Complex.ofReal_mem_slitPlane.mpr hx)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

/-- Assign lower-side values along the negative real cut. -/
noncomputable def BoundaryInternal.minusOneLowerModel (z : ℂ) : ℂ :=
  if z.im = 0 ∧ z.re < 0 then
    minusOneLowerBoundary z.re else (branch (-1)) z

theorem BoundaryInternal.minusOneLowerModel_eq {z : ℂ} (hz : z ∈ branchDomain) :
    BoundaryInternal.minusOneLowerModel z = (branch (-1)) z := by
  have hn : ¬(z.im = 0 ∧ z.re < 0) := by
    rintro ⟨hi, hr⟩
    rcases hz with hz | hz
    · linarith
    · exact hz hi
  simp [BoundaryInternal.minusOneLowerModel, hn]

theorem BoundaryInternal.minusOneLowerModel_ofReal {x : ℝ} (hx : x < 0)
    :
    BoundaryInternal.minusOneLowerModel (x : ℂ) = minusOneLowerBoundary x := by
  simp [BoundaryInternal.minusOneLowerModel, hx]

theorem BoundaryInternal.continuousWithinAt_minusOneLowerModel {x : ℝ} (hx : x < 0)
    :
    ContinuousWithinAt BoundaryInternal.minusOneLowerModel
      (insert (x : ℂ) {z : ℂ | z.im < 0}) (x : ℂ) := by
  apply continuousWithinAt_insert_self.mpr
  change Tendsto BoundaryInternal.minusOneLowerModel _ _
  rw [BoundaryInternal.minusOneLowerModel_ofReal hx]
  apply (tendsto_minusOne_lower_boundary (ne_of_lt hx)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (BoundaryInternal.minusOneLowerModel_eq (Or.inr (ne_of_lt hz))).symm

/-- The lower-side assignment preserves the inverse equation on the negative real cut. -/
theorem BoundaryInternal.mulExp_minusOneLowerModel_ofReal {x : ℝ} (hx : x < 0)
    :
    mulExp (BoundaryInternal.minusOneLowerModel (x : ℂ)) = (x : ℂ) := by
  rw [BoundaryInternal.minusOneLowerModel_ofReal hx]
  exact mulExp_minusOneLowerBoundary (ne_of_lt hx)

/-- The lower-side value at `-1/e` is nonreal, unlike the upper value `-1`. -/
theorem im_minusOneLowerBoundary_le_neg_pi {x : ℝ} (hx : x ≠ 0) :
    (minusOneLowerBoundary x).im ≤ -Real.pi :=
  im_minusOne_lower_limit_le_neg_pi (tendsto_minusOne_lower_boundary hx)

theorem minusOneLowerBoundary_branchPoint_ne_neg_one :
    minusOneLowerBoundary (-Real.exp (-1)) ≠ -1 := by
  intro he
  have hh := im_minusOneLowerBoundary_le_neg_pi (neg_ne_zero.mpr (Real.exp_ne_zero (-1)))
  rw [he] at hh
  norm_num at hh
  linarith [Real.pi_pos]

/-- The two boundary conventions differ throughout the real lower interval. -/
theorem minusOne_boundary_values_ne_on_real_lower {x : ℝ}
    (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    minusOneLowerBoundary x ≠ minusOneUpperBoundary x := by
  intro he
  have hh := im_minusOneLowerBoundary_le_neg_pi (ne_of_lt hx.2)
  rw [he] at hh
  have hu : minusOneUpperBoundary x = (Real.lower x : ℂ) := by
    rw [← BoundaryInternal.minusOneUpperModel_ofReal hx.2]
    exact BoundaryInternal.minusOneUpperModel_eq_real_lower hx
  rw [hu, Complex.ofReal_im] at hh
  linarith [Real.pi_pos]

/-- The lower and upper values are distinct at every negative real input. -/
theorem minusOne_lower_upper_boundary_ne {x : ℝ} (hx : x < 0) :
    minusOneLowerBoundary x ≠ minusOneUpperBoundary x := by
  have hl := im_minusOneLowerBoundary_le_neg_pi (ne_of_lt hx)
  have hu := neg_pi_lt_im_minusOne_upper_limit hx
    (tendsto_minusOne_upper_boundary hx) (mulExp_minusOneUpperBoundary hx)
  intro he
  rw [he] at hl
  linarith

/-- Lower-side analytic extension at every nonzero real input, including `-1/e`. -/
theorem exists_minusOne_lower_extension_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧
      F x = minusOneLowerBoundary x ∧
      (∀ᶠ z in 𝓝 (x : ℂ), mulExp (F z) = z) ∧
      (∀ᶠ z in 𝓝[{z : ℂ | z.im < 0}] (x : ℂ), (branch (-1)) z = F z) := by
  have hn : minusOneLowerBoundary x ≠ -1 := by
    intro he
    have hh := im_minusOneLowerBoundary_le_neg_pi hx
    rw [he] at hh
    norm_num at hh
    linarith [Real.pi_pos]
  obtain ⟨F, hF, hleft, hright⟩ := exists_analytic_localInverse hn
  have hi := mulExp_minusOneLowerBoundary hx
  rw [hi] at hF hright
  have hc : F (x : ℂ) = minusOneLowerBoundary x := by
    simpa only [hi] using hleft.self_of_nhds
  refine ⟨F, hF, hc, hright, ?_⟩
  filter_upwards [(tendsto_minusOne_lower_boundary hx).eventually hleft,
    self_mem_nhdsWithin] with z hz hd
  rw [(mulExp_branch (-1)) (Or.inr (ne_of_lt hd))] at hz
  exact hz.symm

/-- The endpoint value is a noncritical solution of the defining equation. -/
theorem minusOneLowerBoundary_branchPoint_spec :
    mulExp (minusOneLowerBoundary (-Real.exp (-1))) = -Complex.exp (-1) ∧
      (minusOneLowerBoundary (-Real.exp (-1))).im ≤ -Real.pi ∧
      minusOneLowerBoundary (-Real.exp (-1)) ≠ -1 := by
  have hn := neg_ne_zero.mpr (Real.exp_ne_zero (-1))
  exact ⟨by simpa using mulExp_minusOneLowerBoundary hn,
    im_minusOneLowerBoundary_le_neg_pi hn, minusOneLowerBoundary_branchPoint_ne_neg_one⟩

end LambertW.Complex
