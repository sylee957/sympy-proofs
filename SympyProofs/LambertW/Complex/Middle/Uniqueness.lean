import SympyProofs.LambertW.Complex.Middle.Real
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Uniqueness and compatibility of middle-branch continuations

A continuous right inverse taking the real lower value at an interior real
center agrees locally with `localMiddle`. Analytic continuations with that
normalization agree throughout any common connected open domain. These results
establish uniqueness of continuation; they do not assert global existence.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- A continuous right inverse with the middle value at its center is locally
forced to equal the constructed local middle inverse. -/
theorem eventuallyEq_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0)
    {F : ℂ → ℂ} (hF : ContinuousAt F (x : ℂ))
    (hcenter : F (x : ℂ) = (Real.lower x : ℂ))
    (hinv : ∀ᶠ z in 𝓝 (x : ℂ), mulExp (F z) = z) :
    F =ᶠ[𝓝 (x : ℂ)] localMiddle x hx := by
  have ht : Tendsto F (𝓝 (x : ℂ)) (𝓝 (Real.lower x : ℂ)) := by
    simpa only [hcenter] using hF.tendsto
  filter_upwards [ht.eventually (eventually_localMiddle_mulExp hx), hinv] with z hz hi
  rw [hi] at hz
  exact hz.symm

/-- Two continuous middle inverses with the same center agree on a neighborhood. -/
theorem eventuallyEq_middle_inverses {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0)
    {F G : ℂ → ℂ} (hF : ContinuousAt F (x : ℂ)) (hG : ContinuousAt G (x : ℂ))
    (hFc : F (x : ℂ) = (Real.lower x : ℂ))
    (hGc : G (x : ℂ) = (Real.lower x : ℂ))
    (hFi : ∀ᶠ z in 𝓝 (x : ℂ), mulExp (F z) = z)
    (hGi : ∀ᶠ z in 𝓝 (x : ℂ), mulExp (G z) = z) :
    F =ᶠ[𝓝 (x : ℂ)] G :=
  (eventuallyEq_localMiddle hx hF hFc hFi).trans
    (eventuallyEq_localMiddle hx hG hGc hGi).symm

/-- An explicit disk of compatibility for a normalized continuous inverse. -/
theorem exists_pos_eq_localMiddle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0)
    {F : ℂ → ℂ} (hF : ContinuousAt F (x : ℂ))
    (hcenter : F (x : ℂ) = (Real.lower x : ℂ))
    (hinv : ∀ᶠ z in 𝓝 (x : ℂ), mulExp (F z) = z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - (x : ℂ)‖ < r → F z = localMiddle x hx z := by
  obtain ⟨r, hr, h⟩ := Metric.mem_nhds_iff.mp (eventuallyEq_localMiddle hx hF hcenter hinv)
  exact ⟨r, hr, fun z hz => h (by simpa [Metric.mem_ball, dist_eq_norm] using hz)⟩

/-- Uniqueness of analytic continuation on a connected open domain containing
an interior real center, normalized by the real lower value at that center. -/
theorem eqOn_middle_of_isPreconnected {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0)
    (hxU : (x : ℂ) ∈ U) {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hFc : F (x : ℂ) = (Real.lower x : ℂ))
    (hGc : G (x : ℂ) = (Real.lower x : ℂ))
    (hFi : ∀ z ∈ U, mulExp (F z) = z)
    (hGi : ∀ z ∈ U, mulExp (G z) = z) : EqOn F G U := by
  apply hF.eqOn_of_preconnected_of_eventuallyEq hG hconn hxU
  apply eventuallyEq_middle_inverses hx (hF _ hxU).continuousAt (hG _ hxU).continuousAt hFc hGc
  · filter_upwards [hU.mem_nhds hxU] with z hz
    exact hFi z hz
  · filter_upwards [hU.mem_nhds hxU] with z hz
    exact hGi z hz

end LambertW.Complex
