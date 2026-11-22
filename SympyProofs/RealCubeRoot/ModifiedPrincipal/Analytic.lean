module

public import SympyProofs.RealCubeRoot.ModifiedPrincipal.Properties
public import SympyProofs.RealCubeRoot.Analytic

/-!
# Continuity and analyticity of the modified principal cube root

`modifiedPrincipal` is analytic exactly on `slitPlane`, the complement of the
nonpositive real axis, and continuous exactly on `slitPlane` and at zero.

At a negative real `x` it tends to `principal x` from the upper half-plane and
to `conj (principal x)` from the lower half-plane, while its value there is the
real cube root. These are the three cube roots of `x`, so the function is
continuous from neither side. Along the real axis alone it is continuous.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Filter
open scoped Topology ComplexConjugate

/-! ### The sign of the real part at a negative real -/

private theorem modifiedPrincipal_ofReal_re_neg {x : ℝ} (hx : x < 0) :
    (modifiedPrincipal (x : ℂ)).re < 0 := by
  rw [modifiedPrincipal_ofReal, ofReal_re]
  exact realCubicSurd_lt_zero hx

/-! ### Analyticity off the nonpositive real axis -/

/-- Near a point off the nonpositive real axis, the modified root is the principal root. -/
theorem eventuallyEq_modifiedPrincipal_principal {z : ℂ} (hz : z ∈ slitPlane) :
    modifiedPrincipal =ᶠ[𝓝 z] principal := by
  filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
  exact modifiedPrincipal_eq_principal hw

theorem analyticAt_modifiedPrincipal {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ modifiedPrincipal z :=
  (analyticAt_principal hz).congr (eventuallyEq_modifiedPrincipal_principal hz).symm

theorem analyticOnNhd_modifiedPrincipal : AnalyticOnNhd ℂ modifiedPrincipal slitPlane :=
  fun _ hz => analyticAt_modifiedPrincipal hz

theorem differentiableOn_modifiedPrincipal : DifferentiableOn ℂ modifiedPrincipal slitPlane :=
  analyticOnNhd_modifiedPrincipal.differentiableOn

theorem continuousOn_modifiedPrincipal_slitPlane : ContinuousOn modifiedPrincipal slitPlane :=
  analyticOnNhd_modifiedPrincipal.continuousOn

/-! ### Zero -/

/-- The modified root is continuous at zero from every complex direction. -/
theorem continuousAt_modifiedPrincipal_zero : ContinuousAt modifiedPrincipal 0 := by
  have hp : ContinuousAt principal 0 := continuousAt_principal_of_re_nonneg (by simp)
  have hc : ContinuousAt (fun z : ℂ => principal (conj z)) 0 :=
    ContinuousAt.comp (g := principal) (by simpa using hp)
      Complex.continuous_conj.continuousAt
  exact (continuousAt_const.mul hp).add
    (continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp hc))

theorem not_differentiableAt_modifiedPrincipal_zero :
    ¬DifferentiableAt ℂ modifiedPrincipal 0 :=
  not_differentiableAt_zero_of_cube modifiedPrincipal_cube

theorem not_analyticAt_modifiedPrincipal_zero : ¬AnalyticAt ℂ modifiedPrincipal 0 :=
  fun h => not_differentiableAt_modifiedPrincipal_zero h.differentiableAt

/-! ### The negative real axis -/

/-- From the upper half-plane, the limit at a negative real is the principal root. -/
theorem tendsto_modifiedPrincipal_from_above {x : ℝ} (hx : x < 0) :
    Tendsto modifiedPrincipal (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 (principal x)) := by
  have h : Tendsto principal (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 (principal x)) :=
    (continuousWithinAt_principal_of_neg hx).mono (fun w (hw : 0 < w.im) => hw.le)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (modifiedPrincipal_eq_principal (Or.inr (ne_of_gt hw))).symm

/-- From the lower half-plane, the limit at a negative real is the conjugate
of the principal root. -/
theorem tendsto_modifiedPrincipal_from_below {x : ℝ} (hx : x < 0) :
    Tendsto modifiedPrincipal (𝓝[{w : ℂ | w.im < 0}] (x : ℂ))
      (𝓝 (conj (principal x))) := by
  have hconj : Tendsto (fun w : ℂ => conj w) (𝓝[{w : ℂ | w.im < 0}] (x : ℂ))
      (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (Complex.continuous_conj.tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := {w : ℂ | w.im < 0}))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
  have h := (Complex.continuous_conj.tendsto _).comp
    ((tendsto_modifiedPrincipal_from_above hx).comp hconj)
  refine h.congr fun w => ?_
  simp

/-- The value at a negative real is neither of the two one-sided limits. -/
theorem modifiedPrincipal_ofReal_ne_principal {x : ℝ} (hx : x < 0) :
    modifiedPrincipal (x : ℂ) ≠ principal x := by
  intro h
  have h1 := modifiedPrincipal_ofReal_re_neg hx
  rw [h] at h1
  linarith [principal_re_nonneg (x : ℂ)]

theorem modifiedPrincipal_ofReal_ne_conj_principal {x : ℝ} (hx : x < 0) :
    modifiedPrincipal (x : ℂ) ≠ conj (principal x) := by
  intro h
  have h1 := modifiedPrincipal_ofReal_re_neg hx
  rw [h, conj_re] at h1
  linarith [principal_re_nonneg (x : ℂ)]

/-- Discontinuity at a negative real within any set that approaches it through
points off the real axis. -/
private theorem not_continuousWithinAt_modifiedPrincipal {x : ℝ} (hx : x < 0) {s : Set ℂ}
    (hs : ∀ ε > 0, ∃ w ∈ s, w ∈ slitPlane ∧ dist w (x : ℂ) < ε) :
    ¬ContinuousWithinAt modifiedPrincipal s (x : ℂ) := by
  intro h
  have hre : Tendsto (fun w => (modifiedPrincipal w).re) (𝓝[s] (x : ℂ))
      (𝓝 (modifiedPrincipal (x : ℂ)).re) :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt h
  have hev : ∀ᶠ w in 𝓝[s] (x : ℂ), (modifiedPrincipal w).re < 0 :=
    hre.eventually_lt_const (modifiedPrincipal_ofReal_re_neg hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  obtain ⟨w, hws, hw, hd⟩ := hs ε hε
  have hlt : (modifiedPrincipal w).re < 0 := hball ⟨hd, hws⟩
  rw [modifiedPrincipal_eq_principal hw] at hlt
  linarith [principal_re_nonneg w]

/-- The modified root is not continuous from above at a negative real. -/
theorem not_continuousWithinAt_modifiedPrincipal_upper {x : ℝ} (hx : x < 0) :
    ¬ContinuousWithinAt modifiedPrincipal {w : ℂ | 0 ≤ w.im} (x : ℂ) := by
  refine not_continuousWithinAt_modifiedPrincipal hx fun ε hε =>
    ⟨x + ((ε / 2 : ℝ) : ℂ) * I, ?_, Or.inr ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add]
    positivity
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    positivity
  · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith

/-- The modified root is not continuous from below at a negative real. -/
theorem not_continuousWithinAt_modifiedPrincipal_lower {x : ℝ} (hx : x < 0) :
    ¬ContinuousWithinAt modifiedPrincipal {w : ℂ | w.im ≤ 0} (x : ℂ) := by
  refine not_continuousWithinAt_modifiedPrincipal hx fun ε hε =>
    ⟨x - ((ε / 2 : ℝ) : ℂ) * I, ?_, Or.inr ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_sub]
    linarith
  · simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_sub]
    linarith
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith

theorem not_continuousAt_modifiedPrincipal_of_neg {x : ℝ} (hx : x < 0) :
    ¬ContinuousAt modifiedPrincipal (x : ℂ) :=
  fun h => not_continuousWithinAt_modifiedPrincipal_upper hx h.continuousWithinAt

/-- The real cube root is continuous on the whole real line, including zero. -/
theorem continuous_realCubicSurd : Continuous realCubicSurd := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h : ContinuousAt (fun x : ℝ => (modifiedPrincipal (x : ℂ)).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        (ContinuousAt.comp (g := modifiedPrincipal)
          (by simpa using continuousAt_modifiedPrincipal_zero)
          Complex.continuous_ofReal.continuousAt)
    simpa only [modifiedPrincipal_ofReal, ofReal_re] using h
  · exact (analyticAt_realCubicSurd hx).continuousAt

/-- Along the real axis alone, the modified root is continuous. -/
theorem continuousOn_modifiedPrincipal_real :
    ContinuousOn modifiedPrincipal {z : ℂ | z.im = 0} := by
  have hc : Continuous fun z : ℂ => ((realCubicSurd z.re : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_realCubicSurd.comp Complex.continuous_re)
  refine hc.continuousOn.congr fun z hz => ?_
  have hzr : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hz.symm)
  calc
    modifiedPrincipal z = modifiedPrincipal (z.re : ℂ) := by rw [hzr]
    _ = _ := modifiedPrincipal_ofReal z.re

/-! ### Exact domains of continuity and analyticity -/

/-- The modified root is continuous exactly off the negative real axis. -/
theorem continuousAt_modifiedPrincipal_iff {z : ℂ} :
    ContinuousAt modifiedPrincipal z ↔ z ∈ slitPlane ∨ z = 0 := by
  constructor
  · intro h
    by_contra hz
    obtain ⟨hs, h0⟩ := not_or.mp hz
    rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have hzr : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hs.2.symm)
    have hneg : z.re < 0 := lt_of_le_of_ne hs.1 fun hr => h0 (by rw [← hzr, hr]; simp)
    rw [← hzr] at h
    exact not_continuousAt_modifiedPrincipal_of_neg hneg h
  · rintro (hz | rfl)
    · exact (analyticAt_modifiedPrincipal hz).continuousAt
    · exact continuousAt_modifiedPrincipal_zero

/-- The modified root is complex differentiable exactly off the nonpositive real axis. -/
theorem differentiableAt_modifiedPrincipal_iff {z : ℂ} :
    DifferentiableAt ℂ modifiedPrincipal z ↔ z ∈ slitPlane := by
  constructor
  · intro h
    rcases continuousAt_modifiedPrincipal_iff.mp h.continuousAt with hz | rfl
    · exact hz
    · exact absurd h not_differentiableAt_modifiedPrincipal_zero
  · exact fun hz => (analyticAt_modifiedPrincipal hz).differentiableAt

/-- The modified root is analytic exactly off the nonpositive real axis. -/
theorem analyticAt_modifiedPrincipal_iff {z : ℂ} :
    AnalyticAt ℂ modifiedPrincipal z ↔ z ∈ slitPlane :=
  ⟨fun h => differentiableAt_modifiedPrincipal_iff.mp h.differentiableAt,
    analyticAt_modifiedPrincipal⟩

end RealCubeRoot
