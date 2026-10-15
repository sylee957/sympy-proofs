import SympyProofs.LambertW.Complex.Middle.Basic
import SympyProofs.LambertW.ERealContinuity

/-! # Agreement of the local complex middle inverse with the real lower branch -/

open Set Filter Topology

namespace LambertW.Real

/-- The real lower branch is continuous at each interior point of its domain. -/
theorem continuousAt_lower {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ContinuousAt lower x := by
  have he : ContinuousAt EReal.lower (x : EReal) := by
    apply EReal.continuousOn_lower.continuousAt
    apply Icc_mem_nhds
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  have h := he.tendsto.comp (continuous_coe_real_ereal.continuousAt (x := x)).tendsto
  rw [EReal.lower_coe (ne_of_lt hx.2)] at h
  apply EReal.tendsto_coe.mp
  apply h.congr'
  filter_upwards [eventually_lt_nhds hx.2] with y hy
  exact EReal.lower_coe (ne_of_lt hy)

end LambertW.Real

namespace LambertW.Complex

/-- On a real neighborhood of its center, the complex inverse is the real lower branch. -/
theorem eventually_localMiddle_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ∀ᶠ y : ℝ in 𝓝 x, localMiddle x hx (y : ℂ) = (Real.lower y : ℂ) := by
  have hp : Tendsto (fun y : ℝ => (Real.lower y : ℂ)) (𝓝 x)
      (𝓝 (Real.lower x : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (Real.continuousAt_lower hx).tendsto
  have hi := hp.eventually (eventually_localMiddle_mulExp hx)
  filter_upwards [hi, Ioo_mem_nhds hx.1 hx.2] with y hy hdomain
  simpa only [mulExp_ofReal, Real.mulExp_lower ⟨hdomain.1.le, hdomain.2⟩] using hy

/-- A positive radius on which agreement with the real branch holds. -/
theorem exists_pos_localMiddle_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x| < ε →
      localMiddle x hx (y : ℂ) = (Real.lower y : ℂ) := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp (eventually_localMiddle_ofReal hx)
  refine ⟨ε, hε, fun y hy => h ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hy

/-- The local middle branch takes real values on the real axis near its center. -/
theorem eventually_im_localMiddle_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    ∀ᶠ y : ℝ in 𝓝 x, (localMiddle x hx (y : ℂ)).im = 0 := by
  filter_upwards [eventually_localMiddle_ofReal hx] with y hy
  rw [hy, Complex.ofReal_im]

end LambertW.Complex
