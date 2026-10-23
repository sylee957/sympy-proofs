module

public import SympyProofs.RealCubeRoot.CubicSurd

/-!
# Analyticity of the real cube-root branch

The negative real axis lies inside the analytic domain. Zero cannot be an
analytic point of any cube-root function: differentiating `f(z)^3 = z` at zero
would give `0 = 1`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Filter
open scoped Topology

theorem isOpen_analyticDomain : IsOpen analyticDomain :=
  isOpen_ne_fun Complex.continuous_re continuous_const

/-- At a right-half-plane point, the branch agrees locally with the principal root. -/
theorem eventuallyEq_principal {z : ℂ} (hz : 0 < z.re) :
    cubicSurd =ᶠ[𝓝 z] principal := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
    with w hw
  exact cubicSurd_eq_principal hw

/-- At a left-half-plane point, the branch agrees locally with the reflected root. -/
theorem eventuallyEq_neg_principal {z : ℂ} (hz : z.re < 0) :
    cubicSurd =ᶠ[𝓝 z] (fun w => -principal (-w)) := by
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz]
    with w hw
  exact cubicSurd_eq_neg_principal hw

theorem analyticAt_cubicSurd {z : ℂ} (hz : z ∈ analyticDomain) :
    AnalyticAt ℂ cubicSurd z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hs : -z ∈ slitPlane := Or.inl (by simpa using neg_pos.mpr hneg)
    have ha : AnalyticAt ℂ (fun w => -principal (-w)) z :=
      ((analyticAt_principal hs).comp analyticAt_id.neg).neg
    exact ha.congr (eventuallyEq_neg_principal hneg).symm
  · exact (analyticAt_principal (Or.inl hpos)).congr (eventuallyEq_principal hpos).symm

theorem analyticOnNhd_cubicSurd : AnalyticOnNhd ℂ cubicSurd analyticDomain :=
  fun _ hz => analyticAt_cubicSurd hz

theorem differentiableOn_cubicSurd : DifferentiableOn ℂ cubicSurd analyticDomain :=
  analyticOnNhd_cubicSurd.differentiableOn

/-- The cubic surd is continuous at zero from every complex direction. -/
theorem continuousAt_cubicSurd_zero : ContinuousAt cubicSurd 0 := by
  have hp : ContinuousAt principal 0 := continuousAt_principal_of_re_nonneg (by simp)
  have hp' : Tendsto principal (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa [ContinuousAt, principal] using hp
  have hn : Tendsto (fun w : ℂ => -w) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [Pi.neg_def, id_eq, neg_zero] using
      (continuousAt_id (x := (0 : ℂ))).neg.tendsto
  have hn' : Tendsto (fun w : ℂ => -principal (-w)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using (hp'.comp hn).neg
  have hpieces := hn'.if' (p := fun z : ℂ => z.re < 0) hp'
  have hzero : Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝 0) (𝓝 0) := tendsto_const_nhds
  change Tendsto cubicSurd (𝓝 0) (𝓝 (cubicSurd 0))
  rw [cubicSurd_zero]
  exact hzero.if' (p := fun z : ℂ => z.re = 0) hpieces

/-- Continuity holds on `domain`, including zero. -/
theorem continuousOn_cubicSurd : ContinuousOn cubicSurd domain := by
  intro z hz
  rcases hz with hz | rfl
  · exact (analyticAt_cubicSurd hz).continuousAt.continuousWithinAt
  · exact continuousAt_cubicSurd_zero.continuousWithinAt

/-- The restriction to `domain` is a continuous function. -/
theorem continuous_cubicSurd_restrict : Continuous (fun z : domain => cubicSurd z) :=
  continuousOn_iff_continuous_domRestrict.mp continuousOn_cubicSurd

/-- In particular, the real branch is analytic at every nonzero real input. -/
theorem analyticAt_cubicSurd_ofReal {x : ℝ} (hx : x ≠ 0) :
    AnalyticAt ℂ cubicSurd (x : ℂ) :=
  analyticAt_cubicSurd hx

/-- Zero remains nonanalytic, as seen by restricting to the real axis. -/
theorem not_analyticAt_cubicSurd_zero : ¬AnalyticAt ℂ cubicSurd 0 := by
  intro h
  have hr : AnalyticAt ℝ (fun x : ℝ => (cubicSurd (x : ℂ)).re) 0 := h.re_ofReal
  exact not_analyticAt_realCubicSurd_zero (by simpa only [cubicSurd_ofReal,
    Complex.ofReal_re] using hr)

/-- No total cube-root function can be complex differentiable at zero. -/
theorem not_differentiableAt_zero_of_cube {f : ℂ → ℂ}
    (hf : ∀ z, f z ^ 3 = z) : ¬DifferentiableAt ℂ f 0 := by
  intro hd
  have hf0 : f 0 = 0 := by
    have h := hf 0
    exact eq_zero_of_pow_eq_zero h
  have h := hd.hasDerivAt.fun_pow 3
  have hid : HasDerivAt (fun z : ℂ => z) 0 0 := by
    simpa only [Pi.pow_apply, hf, hf0, Nat.cast_ofNat, show 3 - 1 = 2 by decide,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using h
  have := hid.unique (hasDerivAt_id (0 : ℂ))
  norm_num at this

theorem no_entire_cube_root :
    ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z, f z ^ 3 = z := by
  rintro ⟨f, hd, hf⟩
  exact not_differentiableAt_zero_of_cube hf (hd 0)

end RealCubeRoot
