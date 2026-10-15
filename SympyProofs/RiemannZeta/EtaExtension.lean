import SympyProofs.RiemannZeta.PairedSeries
import SympyProofs.RiemannZeta.PathContinuation

/-!
# First extension and its path continuations

The quotient `eta s / (1 - 2^(1-s))` extends the original series wherever
`0 < re s` and its denominator is nonzero. All statements respect this domain;
removal of the additional denominator zeros is not asserted here.
-/

noncomputable section
namespace RiemannZeta

open Set Filter unitInterval
open scoped Topology

def etaFactor (s : ℂ) : ℂ := 1 - (2 : ℂ) ^ (1 - s)

def etaDomain : Set ℂ := {s | 0 < s.re ∧ etaFactor s ≠ 0}

/-- Ambient representative, used on `etaDomain` only. -/
def etaQuotient (s : ℂ) : ℂ := eta s / etaFactor s

theorem differentiable_etaFactor : Differentiable ℂ etaFactor := by
  intro s
  exact (differentiableAt_const 1).sub
    (((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl (by norm_num)))

theorem isOpen_etaDomain : IsOpen etaDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun differentiable_etaFactor.continuous continuous_const)

theorem etaFactor_ne_zero {s : ℂ} (hs : s ∈ rightHalfPlane) : etaFactor s ≠ 0 := by
  have heq : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - s)
  have hlt : ‖(2 : ℂ) ^ (1 - s)‖ < 1 := by
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by exact sub_neg.mpr hs)
  intro h
  have hpow : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h).symm
  simp [hpow] at hlt

theorem rightHalfPlane_subset_etaDomain : rightHalfPlane ⊆ etaDomain := by
  intro s hs
  exact ⟨lt_trans zero_lt_one hs, etaFactor_ne_zero hs⟩

theorem analyticOnNhd_etaQuotient : AnalyticOnNhd ℂ etaQuotient etaDomain := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_etaDomain
  intro s hs
  exact ((differentiableAt_eta hs.1).div (differentiable_etaFactor s) hs.2).differentiableWithinAt

theorem etaQuotient_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    etaQuotient s = series s := by
  rw [etaQuotient, eta_eq_factor_mul_series hs]
  exact mul_div_cancel_left₀ _ (etaFactor_ne_zero hs)

theorem etaQuotient_germ_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    etaQuotient =ᶠ[𝓝 s] series :=
  Filter.eventually_of_mem (isOpen_rightHalfPlane.mem_nhds hs)
    fun _ hz => etaQuotient_eq_series hz

theorem etaDomain_avoids_one {s : ℂ} (hs : s ∈ etaDomain) : s ≠ 1 := by
  intro h
  exact hs.2 (by simp [etaFactor, h])

namespace Continuation

/-- Existence along every path in the first extended domain, starting in the
original right half-plane. -/
def viaEta {a b : ℂ} {γ : Path a b} (ha : a ∈ rightHalfPlane)
    (hγ : ∀ t, γ t ∈ etaDomain) : Continuation γ :=
  ofExtension isOpen_etaDomain analyticOnNhd_etaQuotient hγ ha
    (fun t => etaDomain_avoids_one (hγ t)) (etaQuotient_germ_eq_series ha)

@[simp] theorem endpoint_viaEta {a b : ℂ} {γ : Path a b} (ha : a ∈ rightHalfPlane)
    (hγ : ∀ t, γ t ∈ etaDomain) : (viaEta ha hγ).endpoint = etaQuotient b := rfl

theorem endpoint_eq_etaQuotient {a b : ℂ} {γ : Path a b}
    (F : Continuation γ) (hγ : ∀ t, γ t ∈ etaDomain) : F.endpoint = etaQuotient b :=
  F.endpoint_eq_extension isOpen_etaDomain analyticOnNhd_etaQuotient hγ
    (etaQuotient_germ_eq_series F.start_mem)

/-- Path independence within this proved extension domain. -/
theorem endpoint_eq_of_paths_in_etaDomain {a b : ℂ} {γ δ : Path a b}
    (F : Continuation γ) (G : Continuation δ)
    (hγ : ∀ t, γ t ∈ etaDomain) (hδ : ∀ t, δ t ∈ etaDomain) :
    F.endpoint = G.endpoint :=
  (F.endpoint_eq_etaQuotient hγ).trans (G.endpoint_eq_etaQuotient hδ).symm

end Continuation
end RiemannZeta
