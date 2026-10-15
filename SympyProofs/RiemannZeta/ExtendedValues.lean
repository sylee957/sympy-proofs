import SympyProofs.RiemannZeta.GlobalContinuation
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Zeta with values in the extended complex plane

`OnePoint ℂ` carries the one-point compactification topology (the Riemann
sphere). The pole is assigned infinity, making `extendedZeta` continuous on
all of `ℂ`. The input domain remains `ℂ`.
-/

noncomputable section
namespace RiemannZeta
open Set Filter
open scoped Topology OnePoint

/-- Extended complex values, with a single point at infinity. -/
abbrev ExtendedComplex := OnePoint ℂ

/-- The path-continued zeta function, with its pole represented by infinity. -/
def extendedZeta (s : ℂ) : ExtendedComplex :=
  if s = 1 then ∞ else (continuedZeta s : OnePoint ℂ)

@[simp] theorem extendedZeta_one : extendedZeta 1 = ∞ := by simp [extendedZeta]

theorem extendedZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    extendedZeta s = (continuedZeta s : OnePoint ℂ) := by simp [extendedZeta, hs]

@[simp] theorem extendedZeta_eq_infty_iff (s : ℂ) : extendedZeta s = ∞ ↔ s = 1 := by
  by_cases hs : s = 1 <;> simp [extendedZeta, hs]

theorem extendedZeta_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    extendedZeta s = (series s : OnePoint ℂ) := by
  have hs1 : s ≠ 1 := by intro h; norm_num [rightHalfPlane, h] at hs
  rw [extendedZeta_of_ne_one hs1, continuedZeta_eq_series hs]

/-- The finite values escape every compact set as the input approaches the pole. -/
theorem continuedZeta_tendsto_cocompact :
    Tendsto continuedZeta (𝓝[≠] (1 : ℂ)) (cocompact ℂ) := by
  have hp : Tendsto poleRemoved (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using (differentiable_poleRemoved.continuous.tendsto (1 : ℂ)).mono_left nhdsWithin_le_nhds
  have hn : ∀ᶠ s in 𝓝[≠] (1 : ℂ), poleRemoved s ≠ 0 := hp.eventually_ne one_ne_zero
  have hq : Tendsto (fun s : ℂ => (s - 1) / poleRemoved s)
      (𝓝[≠] 1) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
        have h : Continuous (fun s : ℂ => s - 1) := continuous_id.sub continuous_const
        simpa only [sub_self] using (h.tendsto (1 : ℂ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
      convert hsub.div hp (by norm_num : (1 : ℂ) ≠ 0) using 1
      simp
    · filter_upwards [self_mem_nhdsWithin, hn] with s hs hp0
      exact div_ne_zero (sub_ne_zero.mpr hs) hp0
  have hi := Filter.tendsto_inv₀_nhdsNE_zero.comp hq
  rw [Metric.cobounded_eq_cocompact] at hi
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change ((s - 1) / poleRemoved s)⁻¹ = continuedZeta s
  rw [inv_div, continuedZeta_eq_mellinExtension hs]
  exact (eq_div_iff (sub_ne_zero.mpr hs)).mpr
    (by simpa [mul_comm] using sub_one_mul_mellinExtension hs) |>.symm

/-- In the sphere topology the pole has the actual limit infinity. -/
theorem extendedZeta_tendsto_one :
    Tendsto extendedZeta (𝓝[≠] (1 : ℂ)) (𝓝 ∞) := by
  have h := (OnePoint.tendsto_coe_infty (X := ℂ)).comp
    (continuedZeta_tendsto_cocompact.mono_right cocompact_le_coclosedCompact)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (extendedZeta_of_ne_one hs).symm

theorem continuous_extendedZeta : Continuous extendedZeta := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 1
  · subst s
    rw [continuousAt_iff_punctured_nhds, extendedZeta_one]
    exact extendedZeta_tendsto_one
  · apply (OnePoint.continuous_coe.continuousAt.comp
      (continuedZeta_analytic hs).continuousAt).congr
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact (extendedZeta_of_ne_one hz).symm

@[simp] theorem extendedZeta_zero : extendedZeta 0 = ((-1 / 2 : ℂ) : OnePoint ℂ) := by
  rw [extendedZeta_of_ne_one (by norm_num), continuedZeta_zero]

/-- Continuity at the pole alone forces its value, provided the function
agrees with zeta at every other point. -/
theorem eq_infty_of_continuousAt_one {f : ℂ → ExtendedComplex}
    (hf : ContinuousAt f 1)
    (hagree : ∀ s : ℂ, s ≠ 1 → f s = extendedZeta s) : f 1 = ∞ := by
  have heq : extendedZeta =ᶠ[𝓝[≠] (1 : ℂ)] f := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hagree s hs).symm
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (extendedZeta_tendsto_one.congr' heq)

/-- The continuous sphere-valued extension across the pole is unique. -/
theorem extendedZeta_continuous_unique {f : ℂ → ExtendedComplex}
    (hf : Continuous f)
    (hagree : ∀ s : ℂ, s ≠ 1 → f s = extendedZeta s) : f = extendedZeta := by
  funext s
  by_cases hs : s = 1
  · subst s
    rw [extendedZeta_one]
    exact eq_infty_of_continuousAt_one hf.continuousAt hagree
  · exact hagree s hs

/-- Among assignments at the pole, infinity is exactly the one that gives
continuity; all other values of the function are fixed. -/
theorem continuous_iff_value_at_one {f : ℂ → ExtendedComplex}
    (hagree : ∀ s : ℂ, s ≠ 1 → f s = extendedZeta s) :
    Continuous f ↔ f 1 = ∞ := by
  constructor
  · intro hf
    exact eq_infty_of_continuousAt_one hf.continuousAt hagree
  · intro h1
    have heq : f = extendedZeta := by
      funext s
      by_cases hs : s = 1
      · subst s
        simpa using h1
      · exact hagree s hs
    rw [heq]
    exact continuous_extendedZeta

end RiemannZeta
