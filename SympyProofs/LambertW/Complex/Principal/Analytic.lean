import SympyProofs.LambertW.Complex.Principal.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Analyticity of the principal complex Lambert W branch on its slit domain -/

namespace LambertW.Complex

open Set Filter Topology

/-- The sinc expression removes the apparent singularity of the boundary at imaginary part zero. -/
theorem mem_principalRange_iff_sinc (w : ℂ) :
    w ∈ principalRange ↔ w.im ∈ Ioo (-Real.pi) Real.pi ∧
      -Real.cos w.im / Real.sinc w.im < w.re := by
  by_cases h : w.im = 0
  · simp [principalRange, h]
  · have he : -Real.cos w.im / Real.sinc w.im =
        -w.im * Real.cos w.im / Real.sin w.im := by
      rw [Real.sinc_of_ne_zero h, div_div_eq_mul_div]
      ring
    simp [principalRange, h, he]

private theorem sinc_ne_zero_of_mem_strip {y : ℝ} (hy : y ∈ Ioo (-Real.pi) Real.pi) :
    Real.sinc y ≠ 0 := by
  by_cases h : y = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]
    apply div_ne_zero _ h
    rcases lt_or_gt_of_ne h with hn | hp
    · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hn hy.1)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hp hy.2)

/-- The principal output region is open, including across its real-axis portion. -/
theorem isOpen_principalRange : IsOpen principalRange := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨hstrip, hb⟩ := (mem_principalRange_iff_sinc w).mp hw
  have hc : ContinuousAt (fun z : ℂ => -Real.cos z.im / Real.sinc z.im) w :=
    ((Real.continuous_cos.comp Complex.continuous_im).continuousAt.neg).div
      ((Real.continuous_sinc.comp Complex.continuous_im).continuousAt)
      (sinc_ne_zero_of_mem_strip hstrip)
  have hlo : ∀ᶠ z in nhds w, -Real.pi < z.im :=
    Complex.continuous_im.continuousAt.tendsto.eventually (eventually_gt_nhds hstrip.1)
  have hhi : ∀ᶠ z in nhds w, z.im < Real.pi :=
    Complex.continuous_im.continuousAt.tendsto.eventually (eventually_lt_nhds hstrip.2)
  have hbound : ∀ᶠ z in nhds w, -Real.cos z.im / Real.sinc z.im < z.re := by
    have h := (Complex.continuous_re.continuousAt.sub hc).tendsto.eventually
      (eventually_gt_nhds (sub_pos.mpr hb))
    simpa only [Pi.sub_apply, sub_pos] using h
  filter_upwards [hlo, hhi, hbound] with z hl hh hb
  exact (mem_principalRange_iff_sinc z).mpr ⟨⟨hl, hh⟩, hb⟩

/-- The global principal inverse is complex analytic at every point of the slit domain. -/
theorem analyticAt_principal {z : ℂ} (hz : z ∈ principalDomain) :
    AnalyticAt ℂ principal z := by
  let w := principal z
  have hw : w ∈ principalRange := principal_mem hz
  have he : mulExp w = z := mulExp_principal hz
  have ha := analyticAt_mulExp w
  have hn := deriv_mulExp_ne_zero_of_mem_principalRange hw
  let g := ha.hasStrictDerivAt.localInverse mulExp (deriv mulExp w) w hn
  have hg : AnalyticAt ℂ g z := by simpa [g, he] using ha.analyticAt_localInverse hn
  have hgz : g z = w := by
    have h := ha.hasStrictDerivAt.eventually_left_inverse hn
    simpa [g, he] using h.self_of_nhds
  have hmem : ∀ᶠ y in nhds z, g y ∈ principalRange := by
    have ht : Tendsto g (nhds z) (nhds w) := by
      simpa [hgz] using hg.continuousAt.tendsto
    exact ht.eventually (isOpen_principalRange.mem_nhds hw)
  have hinv : ∀ᶠ y in nhds z, mulExp (g y) = y := by
    simpa [g, he] using ha.hasStrictDerivAt.eventually_right_inverse hn
  apply hg.congr
  filter_upwards [hmem, hinv] with y hy heq
  exact eq_principal_of_mulExp_eq hy heq

/-- Holomorphicity on the full open principal slit domain. -/
theorem analyticOnNhd_principal : AnalyticOnNhd ℂ principal principalDomain :=
  fun _ hz => analyticAt_principal hz

theorem continuousOn_principal : ContinuousOn principal principalDomain :=
  fun _ hz => (analyticAt_principal hz).continuousAt.continuousWithinAt

/-- The derivative formula valid even at zero. -/
theorem deriv_principal {z : ℂ} (hz : z ∈ principalDomain) :
    deriv principal z = (Complex.exp (principal z) * (1 + principal z))⁻¹ := by
  have hp := (analyticAt_principal hz).differentiableAt.hasDerivAt
  have hc := (hasDerivAt_mulExp (principal z)).comp z hp
  have he : (fun y => mulExp (principal y)) =ᶠ[nhds z] (fun y => y) := by
    filter_upwards [isOpen_principalDomain.mem_nhds hz] with y hy
    exact mulExp_principal hy
  have hi := (hasDerivAt_id z).congr_of_eventuallyEq he
  have h := hc.unique hi
  have hn : Complex.exp (principal z) * (1 + principal z) ≠ 0 := by
    rw [← deriv_mulExp]
    exact deriv_mulExp_ne_zero_of_mem_principalRange (principal_mem hz)
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using h

theorem hasDerivAt_principal {z : ℂ} (hz : z ∈ principalDomain) :
    HasDerivAt principal (Complex.exp (principal z) * (1 + principal z))⁻¹ z := by
  rw [← deriv_principal hz]
  exact (analyticAt_principal hz).differentiableAt.hasDerivAt

@[simp] theorem deriv_principal_zero : deriv principal 0 = 1 := by
  simp [deriv_principal zero_mem_principalDomain]

end LambertW.Complex
