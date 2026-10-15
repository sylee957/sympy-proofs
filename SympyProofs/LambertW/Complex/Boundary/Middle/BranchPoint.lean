import SympyProofs.LambertW.Complex.Middle.Global
import SympyProofs.LambertW.Complex.Middle.Definitions

/-! # Compatibility and endpoint extension for the global middle branch -/
namespace LambertW.Complex
open Set Filter Topology

/-- The local slit neighborhood is star-convex about any real point in it. -/
theorem starConvex_branchPointMiddleDomain {x : ℝ}
    (hx : (x : ℂ) ∈ branchPointMiddleDomain) :
    StarConvex ℝ (x : ℂ) branchPointMiddleDomain := by
  let f : ℂ → ℂ := fun z => 2 * Complex.exp 1 * (z + Complex.exp (-1))
  have hcast : f (x : ℂ) = ((2 * Real.exp 1 * (x + Real.exp (-1)) : ℝ) : ℂ) := by
    simp [f]
  have hs : StarConvex ℝ (f (x : ℂ)) Complex.slitPlane := by
    rw [hcast]
    apply Complex.starConvex_ofReal_slitPlane
    exact Complex.ofReal_mem_slitPlane.mp (hcast ▸ hx.1)
  intro y hy a b ha hb hab
  have he : f (a • (x : ℂ) + b • y) = a • f (x : ℂ) + b • f y := by
    simp only [f, Complex.real_smul]
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    linear_combination -2 * Complex.exp 1 * Complex.exp (-1) * hab'
  refine ⟨?_, ?_⟩
  · change f (a • (x : ℂ) + b • y) ∈ Complex.slitPlane
    rw [he]
    exact hs hy.1 ha hb hab
  · change ‖f (a • (x : ℂ) + b • y)‖ < branchPointMiddleRadius ^ 2
    rw [he]
    have hh := (convex_ball (0 : ℂ) (branchPointMiddleRadius ^ 2))
      (show f (x : ℂ) ∈ Metric.ball 0 (branchPointMiddleRadius ^ 2) by
        simpa only [Metric.mem_ball, dist_zero_right] using hx.2)
      (show f y ∈ Metric.ball 0 (branchPointMiddleRadius ^ 2) by
        simpa only [Metric.mem_ball, dist_zero_right] using hy.2) ha hb hab
    simpa [Metric.mem_ball, dist_zero_right] using hh

/-- Global and local constructions agree on their whole common domain. -/
theorem middle_eq_branchPointMiddle {z : ℂ}
    (hz : z ∈ middleDomain) (hb : z ∈ branchPointMiddleDomain) :
    middle z = branchPointMiddle z := by
  have hneg : -Real.exp (-1) < (0 : ℝ) := neg_neg_of_pos (Real.exp_pos (-1))
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (-Real.exp (-1)),
      (x : ℂ) ∈ branchPointMiddleDomain ∧
      branchPointMiddle (x : ℂ) = (Real.lower x : ℂ) ∧
      -Real.exp (-1) < x ∧ x < 0 := by
    filter_upwards [eventually_ofReal_mem_branchPointMiddleDomain,
      eventually_branchPointMiddle_ofReal, self_mem_nhdsWithin,
      (eventually_lt_nhds hneg).filter_mono nhdsWithin_le_nhds] with x hd hr hl hu
    exact ⟨hd, hr, hl, hu⟩
  obtain ⟨x, hxdom, hxreal, hxgt, hxlt⟩ := hev.exists
  have hx : x ∈ Ioo (-Real.exp (-1)) 0 := ⟨hxgt, hxlt⟩
  have hm : (x : ℂ) ∈ middleDomain ∩ branchPointMiddleDomain :=
    ⟨ofReal_mem_middleDomain.mpr hx, hxdom⟩
  have hs := (starConvex_middleDomain hx).inter (starConvex_branchPointMiddleDomain hxdom)
  exact eqOn_middle_of_isPreconnected
    (isOpen_middleDomain.inter isOpen_branchPointMiddleDomain)
    (hs.isPathConnected hm).isConnected.isPreconnected hx hm
    (analyticOnNhd_middle.mono inter_subset_left)
    (analyticOnNhd_branchPointMiddle.mono inter_subset_right)
    (middle_ofReal hx) hxreal
    (fun _ h => mulExp_middle h.1) (fun _ h => mulExp_branchPointMiddle h.2) ⟨hz, hb⟩

theorem middleDomain_parameter_mem_slitPlane {z : ℂ} (hz : z ∈ middleDomain) :
    2 * Complex.exp 1 * (z + Complex.exp (-1)) ∈ Complex.slitPlane := by
  have hp := Real.exp_pos (1 : ℝ)
  change 0 < _ ∨ _ ≠ 0
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  rcases hz with hz | hz
  · right
    exact hz
  · left
    have : 0 < z.re + Real.exp (-1) := by linarith [hz.1]
    positivity

/-- Every point of the global domain sufficiently close to the branch point
lies in the local slit neighborhood. -/
theorem eventually_mem_branchPointMiddleDomain :
    ∀ᶠ z in 𝓝[middleDomain] (-Complex.exp (-1)), z ∈ branchPointMiddleDomain := by
  have hc : Continuous (fun z : ℂ => ‖2 * Complex.exp 1 * (z + Complex.exp (-1))‖) := by
    fun_prop
  have ht : Tendsto (fun z : ℂ => ‖2 * Complex.exp 1 * (z + Complex.exp (-1))‖)
      (𝓝[middleDomain] (-Complex.exp (-1))) (𝓝 0) := by
    simpa using (hc.tendsto (-Complex.exp (-1))).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    ht.eventually (eventually_lt_nhds (sq_pos_of_pos branchPointMiddleRadius_pos))] with z hz hn
  exact ⟨middleDomain_parameter_mem_slitPlane hz, hn⟩

/-- The global branch converges to `-1` from every direction in its domain. -/
theorem tendsto_middle_branchPoint :
    Tendsto middle (𝓝[middleDomain] (-Complex.exp (-1))) (𝓝 (-1)) := by
  have ht : Tendsto branchPointMiddle (𝓝[middleDomain] (-Complex.exp (-1))) (𝓝 (-1)) := by
    simpa using continuousAt_branchPointMiddle_branchPoint.tendsto.mono_left
      (show 𝓝[middleDomain] (-Complex.exp (-1)) ≤ 𝓝 (-Complex.exp (-1)) from nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_mem_branchPointMiddleDomain] with z hz hb
  exact (middle_eq_branchPointMiddle hz hb).symm

/-- Extend the double-cut middle branch to its finite branch-point endpoint. -/
noncomputable def middleWithBranchPoint (z : ℂ) : ℂ :=
  if z = -Complex.exp (-1) then -1 else middle z

@[simp] theorem middleWithBranchPoint_branchPoint :
    middleWithBranchPoint (-Complex.exp (-1)) = -1 := by simp [middleWithBranchPoint]

theorem middleWithBranchPoint_eq_middle {z : ℂ} (hz : z ∈ middleDomain) :
    middleWithBranchPoint z = middle z := by
  simp [middleWithBranchPoint, middleDomain_ne_criticalValue hz]

theorem continuousWithinAt_middleWithBranchPoint :
    ContinuousWithinAt middleWithBranchPoint
      (insert (-Complex.exp (-1)) middleDomain) (-Complex.exp (-1)) := by
  apply continuousWithinAt_insert_self.mpr
  change Tendsto middleWithBranchPoint _ _
  rw [middleWithBranchPoint_branchPoint]
  apply tendsto_middle_branchPoint.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (middleWithBranchPoint_eq_middle hz).symm

theorem continuousOn_middleWithBranchPoint :
    ContinuousOn middleWithBranchPoint (insert (-Complex.exp (-1)) middleDomain) := by
  intro z hz
  rcases hz with rfl | hz
  · exact continuousWithinAt_middleWithBranchPoint
  · apply ContinuousAt.continuousWithinAt
    apply (analyticOnNhd_middle z hz).continuousAt.congr_of_eventuallyEq
    filter_upwards [isOpen_middleDomain.mem_nhds hz] with y hy
    exact middleWithBranchPoint_eq_middle hy

/-- The full convergent Puiseux series and cubic remainder for the global branch. -/
theorem exists_middle_complex_puiseux :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[middleDomain] (-Complex.exp (-1)),
        HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * middleParameter z ^ n)
          (middle z + 1) ∧
        middle z = -1 + middleParameter z - middleParameter z ^ 2 / 3 +
          (11 / 72 : ℂ) * middleParameter z ^ 3 + middleParameter z ^ 4 * R (middleParameter z) := by
  obtain ⟨R, hR, he⟩ := exists_branchPointMiddle_puiseux
  refine ⟨R, hR, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_mem_branchPointMiddleDomain,
    he.filter_mono nhdsWithin_le_nhds] with z hz hb hp
  rw [middle_eq_branchPointMiddle hz hb]
  exact hp

end LambertW.Complex
