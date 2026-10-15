import SympyProofs.RiemannZeta.EtaRemovable
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Path-based zeta continuation on the punctured plane

The Mellin extension supplies existence of local germs along every path
avoiding `1`. Fixed-path uniqueness identifies any certified continuation with
these germs, yielding path independence. `continuedZeta` is defined by choosing
a path from `2` and taking the continued endpoint value away from `1`.
It is a total function on `ℂ`, with the arbitrary value `0` at the pole.
-/

noncomputable section
namespace RiemannZeta

open Set Filter unitInterval
open scoped Topology

namespace Continuation

/-- Existence along every path avoiding the pole, with the starting germ
specified by the original convergent series. -/
def viaMellin {a b : ℂ} {γ : Path a b} (ha : a ∈ rightHalfPlane)
    (hγ : ∀ t, γ t ≠ 1) : Continuation γ :=
  ofExtension isOpen_compl_singleton analyticOnNhd_mellinExtension hγ ha hγ
    (mellinExtension_germ_eq_series ha)

@[simp] theorem endpoint_viaMellin {a b : ℂ} {γ : Path a b} (ha : a ∈ rightHalfPlane)
    (hγ : ∀ t, γ t ≠ 1) : (viaMellin ha hγ).endpoint = mellinExtension b := rfl

theorem endpoint_eq_mellinExtension {a b : ℂ} {γ : Path a b} (F : Continuation γ) :
    F.endpoint = mellinExtension b :=
  F.endpoint_unique (viaMellin F.start_mem F.avoids_one)

/-- Any two paths reaching the same point yield the same value, even if they
start at different points of the original half-plane. -/
theorem path_independent {a a' b : ℂ} {γ : Path a b} {δ : Path a' b}
    (F : Continuation γ) (G : Continuation δ) : F.endpoint = G.endpoint :=
  F.endpoint_eq_mellinExtension.trans G.endpoint_eq_mellinExtension.symm

end Continuation

theorem joinedIn_puncturedPlane {s : ℂ} (hs : s ≠ 1) :
    JoinedIn ({1}ᶜ : Set ℂ) 2 s :=
  (isPathConnected_compl_singleton_of_one_lt_rank
    (by simp [Complex.rank_real_complex]) (1 : ℂ)).joinedIn
      2 (by norm_num) s hs

/-- A path from the initial series domain to any point other than the pole. -/
def pathTo (s : ℂ) (hs : s ≠ 1) : Path (2 : ℂ) s :=
  (joinedIn_puncturedPlane hs).somePath

theorem pathTo_avoids_one (s : ℂ) (hs : s ≠ 1) (t : I) : pathTo s hs t ≠ 1 :=
  (joinedIn_puncturedPlane hs).somePath_mem t

def continuationTo (s : ℂ) (hs : s ≠ 1) : Continuation (pathTo s hs) :=
  Continuation.viaMellin (by norm_num [rightHalfPlane]) (pathTo_avoids_one s hs)

/-- Zeta defined by continuation of the series along a path from `2`, with
arbitrary value `0` at the pole. `Continuation.path_independent` proves the
choice of path immaterial. -/
def continuedZeta (s : ℂ) : ℂ :=
  if hs : s = 1 then 0 else (continuationTo s hs).endpoint

@[simp] theorem continuedZeta_one : continuedZeta 1 = 0 := by
  simp [continuedZeta]

theorem continuedZeta_eq_mellinExtension {s : ℂ} (hs : s ≠ 1) :
    continuedZeta s = mellinExtension s := by
  rw [continuedZeta, dite_eq_right hs]
  rfl

theorem continuedZeta_germ_eq_mellinExtension {s : ℂ} (hs : s ≠ 1) :
    continuedZeta =ᶠ[𝓝 s] mellinExtension := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  exact continuedZeta_eq_mellinExtension hz

theorem exists_continuation_to {s : ℂ} (hs : s ≠ 1) :
    ∃ γ : Path (2 : ℂ) s, Nonempty (Continuation γ) :=
  ⟨pathTo s hs, ⟨continuationTo s hs⟩⟩

theorem continuedZeta_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    continuedZeta s = series s := by
  have hs1 : s ≠ 1 := by intro h; norm_num [rightHalfPlane, h] at hs
  rw [continuedZeta_eq_mellinExtension hs1, mellinExtension_eq_series hs]

theorem endpoint_eq_continuedZeta {a b : ℂ} {γ : Path a b} (F : Continuation γ)
    (hb : b ≠ 1) : F.endpoint = continuedZeta b := by
  rw [continuedZeta_eq_mellinExtension hb]
  exact F.endpoint_eq_mellinExtension

/-- The total function is holomorphic away from its genuine pole. -/
theorem continuedZeta_analytic {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ continuedZeta s :=
  (analyticOnNhd_mellinExtension s hs).congr
    (continuedZeta_germ_eq_mellinExtension hs).symm

/-- The arbitrary assigned value at `1` does not affect the pole's residue. -/
theorem continuedZeta_residue_one :
    Tendsto (fun s => (s - 1) * continuedZeta s) (𝓝[≠] 1) (𝓝 1) := by
  apply mellinExtension_residue_one.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [continuedZeta_eq_mellinExtension hs]

theorem analyticAt_mellinExtension_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    AnalyticAt ℂ mellinExtension s := by
  apply analyticOnNhd_mellinExtension
  change s ≠ 1
  intro h
  norm_num [h] at hs

@[simp] theorem continuedZeta_zero : continuedZeta 0 = -1 / 2 := by
  rw [continuedZeta_eq_mellinExtension (by norm_num), mellinExtension_zero]

theorem continuedZeta_neg_even (n : ℕ) :
    continuedZeta (-2 * ((n : ℂ) + 1)) = 0 := by
  have hs : -2 * ((n : ℂ) + 1) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [continuedZeta_eq_mellinExtension hs, mellinExtension_neg_even]

/-- Uniqueness of the holomorphic extension agreeing with the original sum. -/
theorem extension_unique {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {1}ᶜ)
    (hagree : EqOn f series rightHalfPlane) {s : ℂ} (hs : s ≠ 1) :
    f s = continuedZeta s := by
  have hinit : f =ᶠ[𝓝 (2 : ℂ)] series :=
    Filter.eventually_of_mem (isOpen_rightHalfPlane.mem_nhds
      (by norm_num [rightHalfPlane])) fun z hz => hagree hz
  let F : Continuation (pathTo s hs) :=
    Continuation.ofExtension isOpen_compl_singleton hf
      (pathTo_avoids_one s hs) (by norm_num [rightHalfPlane])
      (pathTo_avoids_one s hs) hinit
  exact endpoint_eq_continuedZeta F hs

end RiemannZeta
