import SympyProofs.LambertW.Complex.Middle.NoEscape
import Mathlib.Topology.UniformSpace.Cauchy

/-! # Finite endpoint limits for bounded lifts away from the critical value -/

namespace LambertW.Complex

open Set Filter Topology

/-- On bounded inverse values whose images stay away from the critical value,
the inverse derivative is uniformly bounded. -/
theorem exists_inverse_derivative_bound {R η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      η ≤ ‖mulExp w + Complex.exp (-1)‖ →
      ‖(Complex.exp w * (1 + w))⁻¹‖ ≤ C := by
  let K : Set ℂ := Metric.closedBall 0 R ∩ {w | η ≤ ‖mulExp w + Complex.exp (-1)‖}
  have hc : Continuous (fun w : ℂ => ‖mulExp w + Complex.exp (-1)‖) := by
    have hm : Continuous mulExp := continuous_iff_continuousAt.mpr
      (fun w => (analyticAt_mulExp w).continuousAt)
    exact (hm.add continuous_const).norm
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const hc)
  have hcont : ContinuousOn (fun w : ℂ => ‖(Complex.exp w * (1 + w))⁻¹‖) K := by
    intro w hw
    have hn : Complex.exp w * (1 + w) ≠ 0 := by
      rw [← deriv_mulExp]
      apply deriv_mulExp_ne_zero
      intro he
      have hh := hw.2
      simp [he, mulExp_neg_one] at hh
      linarith
    exact (((Complex.continuous_exp.continuousAt.mul
      (continuous_const.add continuous_id).continuousAt).inv₀ hn).norm).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont
  refine ⟨max 0 C, le_max_left _ _, fun w hw he => ?_⟩
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨w, ⟨by simpa using hw, he⟩, rfl⟩

/-- A bounded-speed lift that remains bounded and stays uniformly away from
the critical value has a finite left endpoint limit. -/
theorem exists_path_lift_endpoint_of_bounded {F γ F' γ' : ℝ → ℂ} {a b R η M : ℝ}
    (hab : a < b) (hη : 0 < η) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (F' t) t)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hbounded : ∀ t ∈ Ico a b, ‖F t‖ ≤ R)
    (haway : ∀ t ∈ Ico a b, η ≤ ‖γ t + Complex.exp (-1)‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M) :
    ∃ w : ℂ, Tendsto F (𝓝[<] b) (𝓝 w) := by
  obtain ⟨C, hC, hbound⟩ := exists_inverse_derivative_bound (R := R) hη
  have hd : ∀ t ∈ Ico a b, ‖F' t‖ ≤ C * M := by
    intro t ht
    have hc := (hasDerivAt_mulExp (F t)).comp t (hF t ht)
    have he := hc.unique ((hγ t ht).congr_of_eventuallyEq (hi t ht))
    have hn : Complex.exp (F t) * (1 + F t) ≠ 0 := by
      rw [← deriv_mulExp]
      apply deriv_mulExp_ne_zero
      intro hw
      have hh := haway t ht
      have hv := (hi t ht).self_of_nhds
      rw [hw, mulExp_neg_one] at hv
      rw [← hv] at hh
      simp at hh
      linarith
    have hv : F' t = (Complex.exp (F t) * (1 + F t))⁻¹ * γ' t := by
      rw [← he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [hv, norm_mul]
    apply mul_le_mul (hbound _ (hbounded t ht) ?_) (hspeed t ht) (norm_nonneg _) hC
    simpa only [(hi t ht).self_of_nhds] using haway t ht
  let L : NNReal := ⟨C * M, mul_nonneg hC hM⟩
  have hLip : LipschitzOnWith L F (Ico a b) :=
    (convex_Ico a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hF t ht).hasDerivWithinAt) (fun t ht => hd t ht)
  apply cauchy_map_iff_exists_tendsto.mp
  have hf : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  apply hf.map_of_le hLip.uniformContinuousOn
  exact Filter.le_principal_iff.mpr (Ico_mem_nhdsLT hab)

/-- Bounded speed and uniform separation from both singular values force a
finite endpoint limit; boundedness of the lift follows from the no-escape estimate. -/
theorem exists_path_lift_endpoint {F γ F' γ' : ℝ → ℂ} {a b δ η M : ℝ}
    (hab : a < b) (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (F' t) t)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hzero : ∀ t ∈ Ico a b, δ ≤ ‖γ t‖)
    (hcrit : ∀ t ∈ Ico a b, η ≤ ‖γ t + Complex.exp (-1)‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M) :
    ∃ w : ℂ, Tendsto F (𝓝[<] b) (𝓝 w) :=
  exists_path_lift_endpoint_of_bounded hab hη hM hF hγ hi
    (norm_path_lift_le_on_Ico hδ hM hF hγ hi hzero hspeed) hcrit hspeed

/-- The finite-limit result yields an analytic inverse at the input endpoint
which agrees with the path lift for all sufficiently late times. -/
theorem exists_path_lift_endpoint_continuation {F γ F' γ' : ℝ → ℂ}
    {a b δ η M : ℝ} {z : ℂ}
    (hab : a < b) (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (F' t) t)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (hzero : ∀ t ∈ Ico a b, δ ≤ ‖γ t‖)
    (hcrit : ∀ t ∈ Ico a b, η ≤ ‖γ t + Complex.exp (-1)‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M)
    (hγlim : Tendsto γ (𝓝[<] b) (𝓝 z)) (hz : z ≠ -Complex.exp (-1)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      (∀ᶠ y in 𝓝 z, mulExp (g y) = y) ∧
      (∀ᶠ t in 𝓝[<] b, F t = g (γ t)) := by
  obtain ⟨w, hwlim⟩ := exists_path_lift_endpoint hab hδ hη hM hF hγ hi hzero hcrit hspeed
  have hinv : ∀ᶠ t in 𝓝[<] b, mulExp (F t) = γ t := by
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    exact (hi t ht).self_of_nhds
  have he : mulExp w = z := tendsto_nhds_unique
    (((analyticAt_mulExp w).continuousAt.tendsto.comp hwlim).congr' hinv) hγlim
  have hw : w ≠ -1 := by
    intro hh
    rw [hh, mulExp_neg_one] at he
    exact hz he.symm
  obtain ⟨g, hg, hleft, hright⟩ := exists_analytic_localInverse hw
  rw [he] at hg hright
  refine ⟨g, hg, hright, ?_⟩
  filter_upwards [hwlim.eventually hleft, hinv] with t ht hi
  rw [hi] at ht
  exact ht.symm

end LambertW.Complex
