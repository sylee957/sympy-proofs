import SympyProofs.LambertW.Complex.Boundary.Side
import SympyProofs.LambertW.Complex.Middle.Conjugation
import SympyProofs.LambertW.Complex.Middle.Zero
import SympyProofs.LambertW.Complex.Boundary.Middle.BranchPoint

/-! # One-sided analytic extensions at regular real boundary points -/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

/-- Away from the two singular values, the upper restriction extends analytically
across every real boundary point. -/
theorem exists_middle_upper_extension {x : ℝ} (hx0 : x ≠ 0)
    (hxb : x ≠ -Real.exp (-1)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧ mulExp (F x) = x ∧
      ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), middle z = F z := by
  let H : Set ℂ := {z | 0 < z.im}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hconv : Convex ℝ H := by
    intro a ha b hb s t hs ht hst
    change 0 < (s • a + t • b).im
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    change 0 < a.im at ha
    change 0 < b.im at hb
    by_cases hs0 : s = 0
    · have ht1 : t = 1 := by linarith
      simpa [hs0, ht1] using hb
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      nlinarith [mul_pos hsp ha, mul_nonneg ht (le_of_lt hb)]
  have hxc : (x : ℂ) ≠ -Complex.exp (-1) := by
    intro he
    apply hxb
    have hh := congrArg Complex.re he
    simpa [Complex.exp_re] using hh
  have ho : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ -Complex.exp (-1)} := isOpen_ne.inter isOpen_ne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho (x : ℂ)
    ⟨by exact_mod_cast hx0, hxc⟩
  let c : ℂ := (x : ℂ) + (r / 2 : ℝ) * Complex.I
  have hcH : c ∈ H := by change 0 < c.im; simp [c]; linarith
  have hcb : c ∈ Metric.ball (x : ℂ) r := by
    simp only [Metric.mem_ball, dist_eq_norm, c, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one]
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
  have hcD : c ∈ middleDomain := Or.inl (ne_of_gt hcH)
  obtain ⟨F, hF, hFc, hFi⟩ := exists_analytic_inverse_on_starDomain
    (hH.union Metric.isOpen_ball) hstar hc (fun z hz => (hregular z hz).1)
    (fun z hz => (hregular z hz).2) (mulExp_middle hcD)
  have heq : EqOn middle F H := by
    let : PreconnectedSpace H := Subtype.preconnectedSpace hconv.isPreconnected
    have hL : Continuous (fun t : H => middle t) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (analyticOnNhd_middle _ (Or.inl (ne_of_gt t.property))).continuousAt.comp
          continuous_subtype_val.continuousAt)
    have hFc' : Continuous (fun t : H => F t) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (hF _ (Or.inl t.property)).continuousAt.comp continuous_subtype_val.continuousAt)
    have hh := eq_of_continuous_mulExp_lifts hL hFc'
      (fun t => (mulExp_middle (Or.inl (ne_of_gt t.property))).trans
        (hFi _ (Or.inl t.property)).symm)
      (fun t => by
        rw [mulExp_middle (Or.inl (ne_of_gt t.property))]
        exact (hregular t (Or.inl t.property)).2)
      (t₀ := ⟨c, hcH⟩) hFc.symm
    intro z hz
    exact congrFun hh ⟨z, hz⟩
  have hxU : (x : ℂ) ∈ U := Or.inr (Metric.mem_ball_self hr)
  refine ⟨F, hF _ hxU, hFi _ hxU, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact heq hz

/-- Finite upper-side limits exist at every regular real point. -/
theorem exists_middle_upper_limit {x : ℝ} (hx0 : x ≠ 0)
    (hxb : x ≠ -Real.exp (-1)) :
    ∃ w : ℂ, mulExp w = x ∧
      Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w) := by
  obtain ⟨F, hF, hi, he⟩ := exists_middle_upper_extension hx0 hxb
  refine ⟨F x, hi, ?_⟩
  apply (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [he] with z hz
  exact hz.symm

/-- Conjugation converts an upper-side limit into the lower-side limit. -/
theorem tendsto_middle_lowerSide_of_upper {x : ℝ} {w : ℂ}
    (hw : Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w)) :
    Tendsto middle (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (conj w)) := by
  have ht : Tendsto conj (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Complex.continuous_conj.tendsto (x : ℂ)).mono_left
        (show 𝓝[{z : ℂ | z.im < 0}] (x : ℂ) ≤ 𝓝 (x : ℂ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hh := (Complex.continuous_conj.tendsto w).comp (hw.comp ht)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change conj (middle (conj z)) = middle z
  rw [middle_conj (Or.inl (ne_of_lt hz))]
  simp

/-- A real point is approachable from the upper half-plane. -/
theorem nhdsWithin_upper_neBot (x : ℝ) :
    NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) :=
  BoundarySide.nhdsWithin_halfPlane_neBot .upper x

/-- Upper-side limits cannot enter the open principal output region. -/
theorem middle_upper_limit_not_mem_principalRange {x : ℝ} {w : ℂ}
    (hw : Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w)) :
    w ∉ principalRange := by
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := nhdsWithin_upper_neBot x
  apply isOpen_principalRange.isClosed_compl.mem_of_tendsto hw
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact middle_not_mem_principalRange (Or.inl (ne_of_gt hz))

/-- On either open cut, upper and middle boundary limits are distinct conjugates. -/
theorem exists_distinct_middle_cut_limits {x : ℝ}
    (hx : x < -Real.exp (-1) ∨ 0 < x) :
    ∃ w : ℂ, mulExp w = x ∧ w ≠ conj w ∧
      Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w) ∧
      Tendsto middle (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (conj w)) := by
  have hb : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  have hx0 : x ≠ 0 := by rcases hx with hx | hx <;> linarith
  have hxb : x ≠ -Real.exp (-1) := by rcases hx with hx | hx <;> linarith
  obtain ⟨w, hi, ht⟩ := exists_middle_upper_limit hx0 hxb
  refine ⟨w, hi, ?_, ht, tendsto_middle_lowerSide_of_upper ht⟩
  intro he
  have him : w.im = 0 := by
    have := congrArg Complex.im he
    simp only [Complex.conj_im] at this
    linarith
  have hwreal : w = (w.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hre : Real.mulExp w.re = x := by
    rw [hwreal, mulExp_ofReal] at hi
    exact Complex.ofReal_injective hi
  rcases hx with hx | hx
  · have hmin : -Real.exp (-1) ≤ Real.mulExp w.re := by
      rcases le_total w.re (-1) with hh | hh
      · have := Real.strictAntiOn_mulExp.antitoneOn hh (show (-1 : ℝ) ∈ Iic (-1) by simp) hh
        simpa using this
      · have := Real.strictMonoOn_mulExp.monotoneOn
          (show (-1 : ℝ) ∈ Ici (-1) by simp) hh hh
        simpa using this
    linarith
  · have hp : 0 < w.re := by
      have hh : 0 < w.re * Real.exp w.re := by rw [← hre] at hx; exact hx
      exact (mul_pos_iff.mp hh).resolve_right (by intro h; exact (not_lt_of_ge (le_of_lt (Real.exp_pos _))) h.2) |>.1
    apply middle_upper_limit_not_mem_principalRange ht
    rw [hwreal, ofReal_mem_principalRange]
    linarith

/-- Both sides meet at the branch point with the common value `-1`. -/
theorem tendsto_middle_upper_branchPoint :
    Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (-Complex.exp (-1))) (𝓝 (-1)) :=
  tendsto_middle_branchPoint.mono_left (nhdsWithin_mono _
    (fun _ hz => Or.inl (ne_of_gt hz)))

theorem tendsto_middle_lower_branchPoint :
    Tendsto middle (𝓝[{z : ℂ | z.im < 0}] (-Complex.exp (-1))) (𝓝 (-1)) :=
  tendsto_middle_branchPoint.mono_left (nhdsWithin_mono _
    (fun _ hz => Or.inl (ne_of_lt hz)))

/-- On the interior real interval, both side limits are the ordinary real value. -/
theorem tendsto_middle_sides_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (Real.lower x : ℂ)) ∧
    Tendsto middle (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (Real.lower x : ℂ)) := by
  have ht := (analyticOnNhd_middle _ (ofReal_mem_middleDomain.mpr hx)).continuousAt.tendsto
  rw [middle_ofReal hx] at ht
  exact ⟨ht.mono_left nhdsWithin_le_nhds, ht.mono_left nhdsWithin_le_nhds⟩

end LambertW.Complex
