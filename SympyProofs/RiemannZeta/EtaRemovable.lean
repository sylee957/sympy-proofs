import SympyProofs.RiemannZeta.EtaExtension
import SympyProofs.RiemannZeta.MellinExtension
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Removing the extra zeros of the eta denominator

The identity theorem is applied to `(s-1) eta(s)` and
`(1-2^(1-s)) poleRemoved(s)`, both holomorphic on the whole positive
half-plane. This avoids presupposing a value of zeta at the pole.
Every denominator zero other than `1` is then proved removable.
-/

noncomputable section
namespace RiemannZeta

open Complex Set Filter
open scoped Topology

theorem eta_poleRemoved_identity {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * eta s = etaFactor s * poleRemoved s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hc : IsPreconnected {z : ℂ | 0 < z.re} :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => (z - 1) * eta z) {z | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_eta hz)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z => etaFactor z * poleRemoved z) {z | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    exact (differentiable_etaFactor.mul differentiable_poleRemoved).differentiableOn
  have hstart : (fun z => (z - 1) * eta z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => etaFactor z * poleRemoved z) := by
    filter_upwards [isOpen_rightHalfPlane.mem_nhds (by norm_num [rightHalfPlane] :
      (2 : ℂ) ∈ rightHalfPlane)] with z hz
    have hz1 : z ≠ 1 := by intro h; norm_num [rightHalfPlane, h] at hz
    rw [eta_eq_factor_mul_series hz, ← sub_one_mul_mellinExtension hz1,
      mellinExtension_eq_series hz]
    unfold etaFactor
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hc (by norm_num) hstart hs

theorem etaQuotient_eq_mellinExtension {s : ℂ} (hs : s ∈ etaDomain) :
    etaQuotient s = mellinExtension s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (etaDomain_avoids_one hs)
  have hm : eta s = etaFactor s * mellinExtension s := by
    apply mul_left_cancel₀ h1
    rw [eta_poleRemoved_identity hs.1, ← sub_one_mul_mellinExtension (etaDomain_avoids_one hs)]
    ring
  rw [etaQuotient, hm, mul_div_cancel_left₀ _ hs.2]

theorem eta_eq_zero_of_factor_eq_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hfactor : etaFactor s = 0) : eta s = 0 := by
  have h := eta_poleRemoved_identity hs
  rw [hfactor, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hs1)

theorem hasDerivAt_etaFactor (s : ℂ) :
    HasDerivAt etaFactor ((2 : ℂ) ^ (1 - s) * Complex.log 2) s := by
  convert (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).const_cpow
      (Or.inl (by norm_num : (2 : ℂ) ≠ 0))) using 1
  · rfl
  · simp [mul_comm]

theorem etaFactor_eventually_ne_zero (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, etaFactor z ≠ 0 := by
  apply (hasDerivAt_etaFactor s).eventually_ne
  apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  intro h
  have hr := congrArg Complex.re h
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simp [Complex.log_re] at hr
  linarith

/-- At each spurious eta-denominator zero, the quotient has the value supplied
by the holomorphic Mellin extension as its punctured limit. -/
theorem etaQuotient_tendsto_at_denominator_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (_hfactor : etaFactor s = 0) :
    Tendsto etaQuotient (𝓝[≠] s) (𝓝 (mellinExtension s)) := by
  apply ((differentiableAt_mellinExtension hs1).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  have hp : ∀ᶠ z in 𝓝 s, 0 < z.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have hpos : ∀ᶠ z in 𝓝[≠] s, 0 < z.re := hp.filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, etaFactor_eventually_ne_zero s] with z hz hn
  exact (etaQuotient_eq_mellinExtension ⟨hz, hn⟩).symm

/-- The replacement at a denominator zero is holomorphic, not just continuous. -/
theorem analyticAt_eta_replacement {s : ℂ} (_hs : 0 < s.re) (hs1 : s ≠ 1)
    (_hfactor : etaFactor s = 0) : AnalyticAt ℂ mellinExtension s :=
  analyticOnNhd_mellinExtension s hs1

end RiemannZeta
