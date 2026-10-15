import SympyProofs.LambertW.Complex.Middle.Analytic
import SympyProofs.LambertW.Complex.Middle.Uniqueness

/-! # A named middle branch on a slit neighborhood

`branchPointMiddle` is specified on the open set `branchPointMiddleDomain`.
This is a local branch-point construction, not a global indexed `W₋₁`.
-/

namespace LambertW.Complex

open Set Filter Topology

private noncomputable def middleCoordinateInverse : ℂ → ℂ :=
  exists_analytic_middle_slit.choose

/-- Positive radius of the selected analytic inverse, measured in its parameter. -/
noncomputable def branchPointMiddleRadius : ℝ :=
  exists_analytic_middle_slit.choose_spec.choose

private theorem middleCoordinate_spec :
    0 < branchPointMiddleRadius ∧ AnalyticAt ℂ middleCoordinateInverse 0 ∧
      (∀ z : ℂ, 2 * Complex.exp 1 * (z + Complex.exp (-1)) ∈ Complex.slitPlane →
        ‖middleParameter z‖ < branchPointMiddleRadius →
        AnalyticAt ℂ (fun z => -1 + middleCoordinateInverse (middleParameter z)) z ∧
        mulExp (-1 + middleCoordinateInverse (middleParameter z)) = z) ∧
      (∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
        -1 + middleCoordinateInverse (middleParameter (x : ℂ)) = (Real.lower x : ℂ)) ∧
      middleCoordinateInverse 0 = 0 ∧ HasDerivAt middleCoordinateInverse 1 0 ∧
      (∀ᶠ p in 𝓝 0, branchSeries (middleCoordinateInverse p) = p ^ 2) :=
  exists_analytic_middle_slit.choose_spec.choose_spec

theorem branchPointMiddleRadius_pos : 0 < branchPointMiddleRadius := middleCoordinate_spec.1

/-- The branch-point slit neighborhood, expressed in the original input. -/
def branchPointMiddleDomain : Set ℂ :=
  {z | 2 * Complex.exp 1 * (z + Complex.exp (-1)) ∈ Complex.slitPlane ∧
    ‖2 * Complex.exp 1 * (z + Complex.exp (-1))‖ < branchPointMiddleRadius ^ 2}

/-- The complex middle inverse on `branchPointMiddleDomain`.
Values outside this domain are not part of its branch specification. -/
noncomputable def branchPointMiddle (z : ℂ) : ℂ :=
  -1 + middleCoordinateInverse (middleParameter z)

theorem isOpen_branchPointMiddleDomain : IsOpen branchPointMiddleDomain := by
  have hc : Continuous (fun z : ℂ => 2 * Complex.exp 1 * (z + Complex.exp (-1))) := by fun_prop
  exact (Complex.isOpen_slitPlane.preimage hc).inter (isOpen_lt hc.norm continuous_const)

private theorem parameter_lt_radius {z : ℂ} (hz : z ∈ branchPointMiddleDomain) :
    ‖middleParameter z‖ < branchPointMiddleRadius := by
  have h := congrArg norm (middleParameter_sq z)
  rw [norm_pow] at h
  have hr := branchPointMiddleRadius_pos
  have hn := norm_nonneg (middleParameter z)
  have hh := hz.2
  rw [← h] at hh
  nlinarith

theorem analyticOnNhd_branchPointMiddle :
    AnalyticOnNhd ℂ branchPointMiddle branchPointMiddleDomain :=
  fun z hz => (middleCoordinate_spec.2.2.1 z hz.1 (parameter_lt_radius hz)).1

theorem mulExp_branchPointMiddle {z : ℂ} (hz : z ∈ branchPointMiddleDomain) :
    mulExp (branchPointMiddle z) = z :=
  (middleCoordinate_spec.2.2.1 z hz.1 (parameter_lt_radius hz)).2

theorem eventually_branchPointMiddle_ofReal :
    ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)), branchPointMiddle (x : ℂ) = (Real.lower x : ℂ) :=
  middleCoordinate_spec.2.2.2.1

/-- Real points immediately to the right of the branch point lie in the domain. -/
theorem eventually_ofReal_mem_branchPointMiddleDomain :
    ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)), (x : ℂ) ∈ branchPointMiddleDomain := by
  have hc : Continuous (fun x : ℝ =>
      ‖2 * Complex.exp 1 * ((x : ℂ) + Complex.exp (-1))‖) := by fun_prop
  have ht : Tendsto (fun x : ℝ => ‖2 * Complex.exp 1 * ((x : ℂ) + Complex.exp (-1))‖)
      (𝓝[>] (-Real.exp (-1))) (𝓝 0) := by
    simpa using (hc.tendsto (-Real.exp (-1))).mono_left nhdsWithin_le_nhds
  have hr : 0 < branchPointMiddleRadius ^ 2 := sq_pos_of_pos branchPointMiddleRadius_pos
  filter_upwards [self_mem_nhdsWithin, ht.eventually (eventually_lt_nhds hr)] with x hx hn
  refine ⟨?_, hn⟩
  have hp : 0 < 2 * Real.exp 1 * (x + Real.exp (-1)) := by
    have : 0 < x + Real.exp (-1) := by change -Real.exp (-1) < x at hx; linarith
    positivity
  change 0 < (2 * Complex.exp 1 * ((x : ℂ) + Complex.exp (-1))).re ∨ _
  left
  simpa [Complex.mul_re, Complex.exp_re, Complex.exp_im] using hp

/-- The named branch has the usual inverse derivative throughout its domain. -/
theorem deriv_branchPointMiddle {z : ℂ} (hz : z ∈ branchPointMiddleDomain) :
    deriv branchPointMiddle z =
      (Complex.exp (branchPointMiddle z) * (1 + branchPointMiddle z))⁻¹ := by
  have hd := (analyticOnNhd_branchPointMiddle z hz).differentiableAt.hasDerivAt
  have hc := (hasDerivAt_mulExp (branchPointMiddle z)).comp z hd
  have he : (fun y => mulExp (branchPointMiddle y)) =ᶠ[𝓝 z] (fun y => y) := by
    filter_upwards [isOpen_branchPointMiddleDomain.mem_nhds hz] with y hy
    exact mulExp_branchPointMiddle hy
  have h := hc.unique ((hasDerivAt_id z).congr_of_eventuallyEq he)
  have hn : Complex.exp (branchPointMiddle z) * (1 + branchPointMiddle z) ≠ 0 := by
    intro hn
    rw [hn, zero_mul] at h
    exact zero_ne_one h
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa [mul_comm] using h

/-- The slit construction and the real-centered inverse charts describe the
same analytic germ at real centers sufficiently near the branch point. -/
theorem eventually_branchPointMiddle_eq_localMiddle :
    ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
      ∀ hx : x ∈ Ioo (-Real.exp (-1)) 0,
        branchPointMiddle =ᶠ[𝓝 (x : ℂ)] localMiddle x hx := by
  filter_upwards [eventually_ofReal_mem_branchPointMiddleDomain,
    eventually_branchPointMiddle_ofReal] with x hmem heq
  intro hx
  apply eventuallyEq_localMiddle hx
    (analyticOnNhd_branchPointMiddle _ hmem).continuousAt heq
  filter_upwards [isOpen_branchPointMiddleDomain.mem_nhds hmem] with z hz
  exact mulExp_branchPointMiddle hz

theorem branchPointMiddleDomain_nonempty : branchPointMiddleDomain.Nonempty := by
  obtain ⟨x, hx⟩ := eventually_ofReal_mem_branchPointMiddleDomain.exists
  exact ⟨(x : ℂ), hx⟩

/-- The square-root coordinate tends to zero at the branch point from every direction. -/
theorem continuousAt_middleParameter_branchPoint :
    ContinuousAt middleParameter (-Complex.exp (-1)) := by
  have hc : ContinuousAt (fun z : ℂ => 2 * Complex.exp 1 * (z + Complex.exp (-1)))
      (-Complex.exp (-1)) := by fun_prop
  have hs : ContinuousAt Complex.sqrt (2 * Complex.exp 1 *
      (-Complex.exp (-1) + Complex.exp (-1))) := by
    apply Complex.continuousAt_sqrt
    simp
  exact (hs.comp (f := fun z : ℂ => 2 * Complex.exp 1 * (z + Complex.exp (-1))) hc).neg

@[simp] theorem middleParameter_branchPoint : middleParameter (-Complex.exp (-1)) = 0 := by
  simp [middleParameter, Complex.sqrt]

theorem continuousAt_branchPointMiddle_branchPoint :
    ContinuousAt branchPointMiddle (-Complex.exp (-1)) := by
  have hq := middleCoordinate_spec.2.1.continuousAt
  rw [← middleParameter_branchPoint] at hq
  exact continuousAt_const.add (hq.comp continuousAt_middleParameter_branchPoint)

@[simp] theorem branchPointMiddle_branchPoint : branchPointMiddle (-Complex.exp (-1)) = -1 := by
  have hc : Tendsto (fun x : ℝ => branchPointMiddle (x : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (branchPointMiddle (-Complex.exp (-1)))) := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 (-Real.exp (-1)))
        (𝓝 (-Complex.exp (-1))) := by
      simpa using Complex.continuous_ofReal.tendsto (-Real.exp (-1))
    have h := continuousAt_branchPointMiddle_branchPoint.tendsto.comp ht
    apply h.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun x : ℝ => (Real.lower x : ℂ))
      (𝓝[>] (-Real.exp (-1))) (𝓝 (-1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_neg, Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      Real.tendsto_lower_nhdsGT_branchPoint
  apply tendsto_nhds_unique hc
  apply hr.congr'
  filter_upwards [eventually_branchPointMiddle_ofReal] with x hx
  exact hx.symm

/-- Convergent Puiseux series and analytic cubic remainder for the local branch. -/
theorem exists_branchPointMiddle_puiseux :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝 (-Complex.exp (-1)),
        HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * middleParameter z ^ n)
          (branchPointMiddle z + 1) ∧
        branchPointMiddle z = -1 + middleParameter z - middleParameter z ^ 2 / 3 +
          (11 / 72 : ℂ) * middleParameter z ^ 3 + middleParameter z ^ 4 * R (middleParameter z) := by
  have hQ := middleCoordinate_spec.2.1
  obtain ⟨hQ0, hdQ, he⟩ := middleCoordinate_spec.2.2.2.2
  obtain ⟨R, hR, hrem⟩ := puiseux_inverse_cubic_remainder hQ hQ0 hdQ he
  obtain ⟨r, hr, hsum⟩ := exists_pos_hasSum_puiseuxCoeff hQ hQ0 hdQ he
  have ht : Tendsto middleParameter (𝓝 (-Complex.exp (-1))) (𝓝 0) := by
    simpa using continuousAt_middleParameter_branchPoint.tendsto
  refine ⟨R, hR, ?_⟩
  filter_upwards [ht.eventually hrem, ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)]
    with z hz hn
  have hn' : ‖middleParameter z‖ < r := by simpa using hn
  constructor
  · simpa [branchPointMiddle] using hsum _ hn'
  · dsimp [branchPointMiddle]
    linear_combination hz

end LambertW.Complex
