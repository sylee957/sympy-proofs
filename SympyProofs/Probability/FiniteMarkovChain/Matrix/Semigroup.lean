module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# From a semigroup back to its generator

`Generator` starts from a generator `Q` and shows that the matrices `transition Q t`
are row stochastic and satisfy the semigroup law. This file goes the other way. A family
of row-stochastic matrices `P t` with `P 0 = 1` and `P (s + t) = P s * P t` that is
continuous at time `0` is `transition Q` for exactly one generator `Q`. This is
`existsUnique_generator_of_semigroup`.

The existence part is a fact about Banach algebras, `exists_eq_exp_of_semigroup`:
a one-parameter semigroup that is continuous at `0` is an exponential. Its proof
integrates the semigroup over a short interval. That integral is invertible, and the
semigroup law turns multiplication by it into a difference of integrals, which is
differentiable. Continuity at `0` cannot be dropped: a constant projection for
positive times and the identity at time `0` is a semigroup with no generator.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Set Filter Topology NormedSpace
open scoped NNReal

section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸]

variable [CompleteSpace 𝔸]

/-- A one-parameter semigroup that is continuous at time `0` is continuous at every
nonnegative time. -/
theorem continuousOn_of_semigroup (P : ℝ → 𝔸) (h0 : P 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = P s * P t)
    (hc : ContinuousWithinAt P (Ici 0) 0) : ContinuousOn P (Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have hsplit : Ici (0 : ℝ) = Ici t ∪ Icc 0 t := by
    ext u
    simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hu
      rcases le_total t u with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hu, h⟩
    · rintro (h | h)
      · exact ht0.trans h
      · exact h.1
  have hc1 : Tendsto P (𝓝[Ici 0] 0) (𝓝 1) := h0 ▸ hc
  rw [ContinuousWithinAt, hsplit, nhdsWithin_union, tendsto_sup]
  constructor
  · -- from the right: `P u = P t * P (u - t)`
    have hsub : Tendsto (fun u : ℝ => u - t) (𝓝[Ici t] t) (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (t - t)) :=
          (continuous_id.sub continuous_const).tendsto t
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact sub_nonneg.2 (show t ≤ u from hu)
    have hlim : Tendsto (fun u : ℝ => P t * P (u - t)) (𝓝[Ici t] t) (𝓝 (P t * 1)) :=
      tendsto_const_nhds.mul (hc1.comp hsub)
    rw [mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : t ≤ u := hu
    rw [← hadd t (u - t) ht0 (sub_nonneg.2 hu')]
    congr 1
    ring
  · -- from the left: `P t = P u * P (t - u)` and `P (t - u)` is invertible near `t`
    have hsub : Tendsto (fun u : ℝ => t - u) (𝓝[Icc 0 t] t) (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun u : ℝ => t - u) (𝓝 t) (𝓝 (t - t)) :=
          (continuous_const.sub continuous_id).tendsto t
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact sub_nonneg.2 hu.2
    have hP : Tendsto (fun u : ℝ => P (t - u)) (𝓝[Icc 0 t] t) (𝓝 1) := hc1.comp hsub
    have hinv : Tendsto (fun u : ℝ => Ring.inverse (P (t - u))) (𝓝[Icc 0 t] t) (𝓝 1) := by
      have h1 : ContinuousAt Ring.inverse ((1 : 𝔸ˣ) : 𝔸) := NormedRing.inverse_continuousAt 1
      have h2 : Tendsto Ring.inverse (𝓝 (1 : 𝔸)) (𝓝 (1 : 𝔸)) := by
        simpa [ContinuousAt] using h1
      exact h2.comp hP
    have hunit : ∀ᶠ u in 𝓝[Icc 0 t] t, IsUnit (P (t - u)) :=
      hP.eventually (Units.isOpen.mem_nhds isUnit_one)
    have hlim : Tendsto (fun u : ℝ => P t * Ring.inverse (P (t - u))) (𝓝[Icc 0 t] t)
        (𝓝 (P t * 1)) := tendsto_const_nhds.mul hinv
    rw [mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hunit] with u hu hunit
    have h1 : P t = P u * P (t - u) := by
      rw [← hadd u (t - u) hu.1 (sub_nonneg.2 hu.2)]
      congr 1
      ring
    rw [h1, mul_assoc, Ring.mul_inverse_cancel _ hunit, mul_one]

variable [NormedAlgebra ℝ 𝔸]

/-- A one-parameter semigroup in a Banach algebra that is continuous at time `0` is an
exponential. -/
theorem exists_eq_exp_of_semigroup (P : ℝ → 𝔸) (h0 : P 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = P s * P t)
    (hc : ContinuousWithinAt P (Ici 0) 0) :
    ∃ Q : 𝔸, ∀ t, 0 ≤ t → P t = exp (t • Q) := by
  have hcon : ContinuousOn P (Ici 0) := continuousOn_of_semigroup P h0 hadd hc
  -- a continuous extension to all real times, and its integral
  let R : ℝ → 𝔸 := fun t => P (max t 0)
  have hR : Continuous R :=
    hcon.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hRP : ∀ t, 0 ≤ t → R t = P t := fun t ht => by simp [R, max_eq_left ht]
  let V : ℝ → 𝔸 := fun t => ∫ s in (0 : ℝ)..t, R s
  have hV : ∀ t, HasDerivAt V (R t) t := fun t =>
    (hR.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hV0 : V 0 = 0 := by simp [V]
  -- the integral over a short interval is invertible
  obtain ⟨ε, hε, u, hu⟩ : ∃ ε : ℝ, 0 < ε ∧ ∃ u : 𝔸ˣ, (u : 𝔸) = V ε := by
    have hs := (hV 0).tendsto_slope_zero_right
    have h1 : R 0 = 1 := by rw [hRP 0 le_rfl, h0]
    rw [h1] at hs
    have hev := hs.eventually (Units.isOpen.mem_nhds isUnit_one)
    obtain ⟨ε, hεu, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε' : (0 : ℝ) < ε := hε
    refine ⟨ε, hε', ?_⟩
    simp only [zero_add, hV0, sub_zero] at hεu
    have h2 : IsUnit (Units.mk0 ε hε'.ne' • (ε⁻¹ • V ε)) := hεu.smul _
    rw [Units.smul_def, Units.val_mk0, smul_smul, mul_inv_cancel₀ hε'.ne', one_smul] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, hu⟩
  have hVu : V ε * (↑u⁻¹ : 𝔸) = 1 := by rw [← hu]; exact u.mul_inv
  -- the semigroup law turns `P h * V ε` into a difference of integrals
  have key : ∀ h, 0 ≤ h → P h * V ε = V (h + ε) - V h := by
    intro h hh
    have e1 : P h * V ε = ∫ s in (0 : ℝ)..ε, P h * R s :=
      ((ContinuousLinearMap.mul ℝ 𝔸 (P h)).intervalIntegral_comp_comm
        (hR.intervalIntegrable 0 ε)).symm
    have e2 : (∫ s in (0 : ℝ)..ε, P h * R s) = ∫ s in (0 : ℝ)..ε, R (s + h) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hε.le] at hs
      simp only
      rw [hRP s hs.1, hRP (s + h) (add_nonneg hs.1 hh), add_comm s h, hadd h s hh hs.1]
    rw [e1, e2, intervalIntegral.integral_comp_add_right, zero_add, add_comm ε h]
    exact (intervalIntegral.integral_interval_sub_left (hR.intervalIntegrable 0 (h + ε))
      (hR.intervalIntegrable 0 h)).symm
  let Q : 𝔸 := (P ε - 1) * (↑u⁻¹ : 𝔸)
  let G : ℝ → 𝔸 := fun h => (V (h + ε) - V h) * (↑u⁻¹ : 𝔸)
  have hG : ∀ h, 0 ≤ h → G h = P h := by
    intro h hh
    simp only [G]
    rw [← key h hh, mul_assoc, hVu, mul_one]
  have hGd : ∀ h, 0 ≤ h → HasDerivAt G (G h * Q) h := by
    intro h hh
    have hd : HasDerivAt G ((R (h + ε) - R h) * (↑u⁻¹ : 𝔸)) h :=
      ((HasDerivAt.comp_add_const h ε (hV (h + ε))).sub (hV h)).mul_const _
    convert hd using 1
    rw [hG h hh, hRP h hh, hRP (h + ε) (add_nonneg hh hε.le), hadd h ε hh hε.le]
    simp only [Q]
    rw [← mul_assoc, mul_sub, mul_one]
  -- `G t * exp (-t Q)` has zero derivative, so it is constant
  let F : ℝ → 𝔸 := fun t => G t * exp (t • -Q)
  have hFd : ∀ t, 0 ≤ t → HasDerivAt F 0 t := by
    intro t ht
    have hd := (hGd t ht).mul (hasDerivAt_exp_smul_const' (-Q) t)
    convert hd using 1
    rw [mul_assoc, ← mul_add, neg_mul, add_neg_cancel, mul_zero]
  have hGcont : Continuous G := by
    have : Continuous V := continuous_iff_continuousAt.2 fun t => (hV t).continuousAt
    fun_prop
  have hFcont : Continuous F := by
    have hE : Continuous fun t : ℝ => exp (t • -Q) :=
      continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (-Q) t).continuousAt
    exact hGcont.mul hE
  refine ⟨Q, fun t ht => ?_⟩
  have hconst : F t = F 0 :=
    constant_of_has_deriv_right_zero hFcont.continuousOn
      (fun x hx => (hFd x hx.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  have hF0 : F 0 = 1 := by simp [F, hG 0 le_rfl, h0]
  have hE : exp (t • -Q) * exp (t • Q) = 1 := by
    have hball : ∀ x : 𝔸, x ∈ Metric.eball (0 : 𝔸) (expSeries ℝ 𝔸).radius := fun x =>
      (expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
    rw [smul_neg, ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.refl (t • Q)).neg_left
      (hball _) (hball _), neg_add_cancel, exp_zero]
  calc P t = G t * (exp (t • -Q) * exp (t • Q)) := by rw [hE, mul_one, hG t ht]
    _ = F t * exp (t • Q) := by simp only [F, mul_assoc]
    _ = exp (t • Q) := by rw [hconst, hF0, one_mul]

end BanachAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A semigroup of row-stochastic matrices that is continuous at time `0` consists of
the transition matrices of exactly one generator. -/
theorem existsUnique_generator_of_semigroup (P : ℝ≥0 → Matrix ι ι ℝ)
    (hP : ∀ t, P t ∈ Matrix.rowStochastic ℝ ι) (h0 : P 0 = 1)
    (hadd : ∀ s t, P (s + t) = P s * P t) (hc : ContinuousAt P 0) :
    ∃! Q : Matrix ι ι ℝ, IsGenerator Q ∧ ∀ t : ℝ≥0, P t = transition Q t := by
  have hex : ∃ Q : Matrix ι ι ℝ, ∀ t : ℝ, 0 ≤ t → P t.toNNReal = transition Q t := by
    open scoped Matrix.Norms.Operator in
      exact exists_eq_exp_of_semigroup (fun t : ℝ => P t.toNNReal) (by simpa using h0)
        (fun s t hs ht => by simp only [Real.toNNReal_add hs ht, hadd])
        (hc.comp_of_eq continuous_real_toNNReal.continuousAt (by simp)).continuousWithinAt
  obtain ⟨Q, hQ⟩ := hex
  have hPQ : ∀ t : ℝ≥0, P t = transition Q t := fun t => by
    simpa using hQ t t.coe_nonneg
  refine ⟨Q, ⟨isGenerator_of_transition_mem_rowStochastic fun t ht => ?_, hPQ⟩,
    fun Q' hQ' => transition_injective fun t => (hQ'.2 t).symm.trans (hPQ t)⟩
  rw [← hQ t ht]
  exact hP _

end SympyProofs.FiniteMarkovChain
