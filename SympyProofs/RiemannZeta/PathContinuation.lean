import SympyProofs.RiemannZeta.RightHalfPlane
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Clopen

/-!
# Analytic continuation along a path

A continuation consists of a holomorphic representative near each point of a
path. Nearby representatives agree as germs, i.e. on a neighborhood, not just
at a point. The identity theorem proves uniqueness along a fixed path.

`Continuation` specializes this to the zeta series at the starting point.
Existence is constructed for paths inside the original right half-plane.
Existence for arbitrary paths avoiding `1`, and independence of the path, are
separate obligations and are not assumed by this file.
-/

noncomputable section
namespace RiemannZeta

open Set Filter Metric unitInterval
open scoped Topology

/-- Local analytic representatives coherently transported along a path. -/
structure AnalyticAlong {a b : ℂ} (γ : Path a b) where
  /-- A representative of the analytic germ at each path parameter. -/
  fn : I → ℂ → ℂ
  radius : I → ℝ
  radius_pos : ∀ t, 0 < radius t
  analytic : ∀ t, AnalyticOnNhd ℂ (fn t) (ball (γ t) (radius t))
  /-- Nearby parameters use the same local holomorphic function. -/
  coherent : ∀ t, ∀ᶠ u in 𝓝 t, fn u =ᶠ[𝓝 (γ u)] fn t

namespace AnalyticAlong

variable {a b : ℂ} {γ : Path a b}

/-- Germ equality between two continuations is locally constant along the path. -/
theorem eventually_germ_eq_iff (F G : AnalyticAlong γ) (t : I) :
    ∀ᶠ u in 𝓝 t,
      (F.fn u =ᶠ[𝓝 (γ u)] G.fn u) ↔ (F.fn t =ᶠ[𝓝 (γ t)] G.fn t) := by
  let r := min (F.radius t) (G.radius t)
  have hr : 0 < r := lt_min (F.radius_pos t) (G.radius_pos t)
  have hf : AnalyticOnNhd ℂ (F.fn t) (ball (γ t) r) :=
    (F.analytic t).mono (ball_subset_ball (min_le_left _ _))
  have hg : AnalyticOnNhd ℂ (G.fn t) (ball (γ t) r) :=
    (G.analytic t).mono (ball_subset_ball (min_le_right _ _))
  have hc : IsPreconnected (ball (γ t) r) := (convex_ball (γ t) r).isPreconnected
  have ht : γ t ∈ ball (γ t) r := mem_ball_self hr
  have hpath : ∀ᶠ u in 𝓝 t, γ u ∈ ball (γ t) r :=
    γ.continuous.continuousAt (isOpen_ball.mem_nhds ht)
  filter_upwards [F.coherent t, G.coherent t, hpath] with u hF hG hu
  constructor
  · intro h
    have hfg := hf.eqOn_of_preconnected_of_eventuallyEq hg hc hu
      (hF.symm.trans (h.trans hG))
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds ht) fun z hz => hfg hz
  · intro h
    have hfg := hf.eqOn_of_preconnected_of_eventuallyEq hg hc ht h
    have hnear : F.fn t =ᶠ[𝓝 (γ u)] G.fn t :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hu) fun z hz => hfg hz
    exact hF.trans (hnear.trans hG.symm)

/-- Two continuations with the same starting germ have the same germ everywhere
along this path. This is fixed-path uniqueness, not path independence. -/
theorem germ_unique (F G : AnalyticAlong γ)
    (hstart : F.fn 0 =ᶠ[𝓝 a] G.fn 0) (t : I) :
    F.fn t =ᶠ[𝓝 (γ t)] G.fn t := by
  let S : Set I := {u | F.fn u =ᶠ[𝓝 (γ u)] G.fn u}
  have hopen : IsOpen S := by
    apply isOpen_iff_eventually.mpr
    intro u hu
    exact (F.eventually_germ_eq_iff G u).mono fun v hv => hv.mpr hu
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_eventually.mpr
    intro u hu
    exact (F.eventually_germ_eq_iff G u).mono fun v hv h => hu (hv.mp h)
  have h0 : (0 : I) ∈ S := by simpa [S] using hstart
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ ⟨0, h0⟩
  have ht : t ∈ S := hall ▸ mem_univ t
  exact ht

/-- Transporting a function already holomorphic on an open set along a path in it. -/
def ofAnalyticOnNhd {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hγ : ∀ t, γ t ∈ U) : AnalyticAlong γ where
  fn _ := f
  radius t := (Metric.isOpen_iff.mp hU (γ t) (hγ t)).choose
  radius_pos t := (Metric.isOpen_iff.mp hU (γ t) (hγ t)).choose_spec.1
  analytic t := hf.mono (Metric.isOpen_iff.mp hU (γ t) (hγ t)).choose_spec.2
  coherent _ := Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl

/-- A continuous change of speed transports the same analytic germs. -/
def reparam (F : AnalyticAlong γ) (ρ : I → I) (hρ : Continuous ρ)
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) : AnalyticAlong (γ.reparam ρ hρ h₀ h₁) where
  fn t := F.fn (ρ t)
  radius t := F.radius (ρ t)
  radius_pos t := F.radius_pos (ρ t)
  analytic t := F.analytic (ρ t)
  coherent t := (hρ.continuousAt.eventually (F.coherent (ρ t)))

end AnalyticAlong

/-- A continuation of the defining zeta germ along a path avoiding its proposed pole.
This is data with proofs; it does not assert that every such path has a continuation. -/
structure Continuation {a b : ℂ} (γ : Path a b) extends AnalyticAlong γ where
  start_mem : a ∈ rightHalfPlane
  avoids_one : ∀ t, γ t ≠ 1
  initial : fn 0 =ᶠ[𝓝 a] series

namespace Continuation

variable {a b : ℂ} {γ : Path a b}

/-- Value reached at the endpoint by a certified continuation. -/
def endpoint (F : Continuation γ) : ℂ := F.fn 1 b

theorem germ_unique (F G : Continuation γ) (t : I) :
    F.fn t =ᶠ[𝓝 (γ t)] G.fn t :=
  F.toAnalyticAlong.germ_unique G.toAnalyticAlong (F.initial.trans G.initial.symm) t

theorem endpoint_unique (F G : Continuation γ) : F.endpoint = G.endpoint := by
  have h := (F.germ_unique G 1).eq_of_nhds
  simpa [endpoint] using h

/-- Turn a proved holomorphic extension into a continuation along any path in its
domain. Agreement with the original series is required as a germ at the start. -/
def ofExtension {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hγ : ∀ t, γ t ∈ U)
    (ha : a ∈ rightHalfPlane) (havoid : ∀ t, γ t ≠ 1)
    (hinit : f =ᶠ[𝓝 a] series) : Continuation γ where
  toAnalyticAlong := AnalyticAlong.ofAnalyticOnNhd hU hf hγ
  start_mem := ha
  avoids_one := havoid
  initial := hinit

/-- Certified continuations agree with any holomorphic extension on a domain
containing the path and agreeing with the initial germ. -/
theorem endpoint_eq_extension (F : Continuation γ) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hγ : ∀ t, γ t ∈ U)
    (hinit : f =ᶠ[𝓝 a] series) : F.endpoint = f b :=
  F.endpoint_unique (ofExtension hU hf hγ F.start_mem F.avoids_one hinit)

/-- Reparametrizing the path transports a zeta continuation. -/
def reparam (F : Continuation γ) (ρ : I → I) (hρ : Continuous ρ)
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) : Continuation (γ.reparam ρ hρ h₀ h₁) where
  toAnalyticAlong := F.toAnalyticAlong.reparam ρ hρ h₀ h₁
  start_mem := F.start_mem
  avoids_one t := F.avoids_one (ρ t)
  initial := by simpa only [AnalyticAlong.reparam, h₀] using F.initial

@[simp] theorem endpoint_reparam (F : Continuation γ) (ρ : I → I) (hρ : Continuous ρ)
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) :
    (F.reparam ρ hρ h₀ h₁).endpoint = F.endpoint := by
  simp only [endpoint, reparam, AnalyticAlong.reparam, h₁]

/-- A concrete continuation along any path staying in the defining half-plane. -/
def inRightHalfPlane (hγ : ∀ t, γ t ∈ rightHalfPlane) : Continuation γ where
  toAnalyticAlong := AnalyticAlong.ofAnalyticOnNhd isOpen_rightHalfPlane analyticOnNhd_series hγ
  start_mem := by simpa using hγ 0
  avoids_one t := by
    have ht := hγ t
    intro h
    simp [rightHalfPlane, h] at ht
  initial := Filter.EventuallyEq.rfl

@[simp] theorem endpoint_inRightHalfPlane (hγ : ∀ t, γ t ∈ rightHalfPlane) :
    (inRightHalfPlane hγ).endpoint = series b := rfl

/-- Every continuation along a path in the original domain recovers its series value. -/
theorem endpoint_eq_series (F : Continuation γ) (hγ : ∀ t, γ t ∈ rightHalfPlane) :
    F.endpoint = series b := F.endpoint_unique (inRightHalfPlane hγ)

end Continuation
end RiemannZeta
