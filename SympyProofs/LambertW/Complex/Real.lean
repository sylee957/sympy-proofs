import SympyProofs.LambertW.Complex.Basic
import SympyProofs.LambertW.ERealContinuity

/-!
# Agreement of the local complex and real principal branches

The complex local inverse constructed at zero agrees with the real principal
branch on a real neighborhood of zero. No global complex branch is assumed.
-/

open Filter Topology Set

namespace LambertW.Real

/-- Continuity at zero, inherited from the continuous extended real branch. -/
theorem continuousAt_principal_zero : ContinuousAt principal 0 := by
  have he : ContinuousAt EReal.principal (0 : EReal) := by
    apply EReal.continuousOn_principal.continuousAt
    apply Ici_mem_nhds
    exact_mod_cast (neg_neg_of_pos (Real.exp_pos (-1)))
  have h := he.tendsto.comp (continuous_coe_real_ereal.continuousAt (x := (0 : ℝ))).tendsto
  apply EReal.tendsto_coe.mp
  simpa [Function.comp_def] using h

end LambertW.Real

namespace LambertW.Complex

/-- On a real neighborhood of zero, the local complex inverse equals the real principal branch. -/
theorem eventually_localPrincipal_ofReal :
    ∀ᶠ x : ℝ in nhds 0, localPrincipal (x : ℂ) = (Real.principal x : ℂ) := by
  have hp : Tendsto (fun x : ℝ => (Real.principal x : ℂ)) (nhds 0) (nhds 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      Real.continuousAt_principal_zero.tendsto
  have hi := hp.eventually eventually_localPrincipal_mulExp
  have hd : ∀ᶠ x : ℝ in nhds 0, -Real.exp (-1) ≤ x :=
    eventually_ge_nhds (neg_neg_of_pos (Real.exp_pos (-1)))
  filter_upwards [hi, hd] with x hx hdomain
  simpa only [mulExp_ofReal, Real.mulExp_principal hdomain] using hx

/-- An explicit positive radius on which both principal constructions agree. -/
theorem exists_pos_localPrincipal_ofReal :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε →
      localPrincipal (x : ℂ) = (Real.principal x : ℂ) := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.mp eventually_localPrincipal_ofReal
  refine ⟨ε, hε, fun x hx => h ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hx

/-- In particular, the local principal branch is real-valued on a real neighborhood of zero. -/
theorem eventually_im_localPrincipal_ofReal :
    ∀ᶠ x : ℝ in nhds 0, (localPrincipal (x : ℂ)).im = 0 := by
  filter_upwards [eventually_localPrincipal_ofReal] with x hx
  rw [hx, Complex.ofReal_im]

end LambertW.Complex
