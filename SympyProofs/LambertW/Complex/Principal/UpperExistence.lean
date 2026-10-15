import SympyProofs.LambertW.Complex.Principal.Upper
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Endpoint limits and solvability of the upper-half-plane magnitude equation -/

namespace LambertW.Complex

open Set Filter Topology

/-- At the right endpoint the magnitude tends to zero. -/
theorem tendsto_upperRadius_nhdsLT {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    Tendsto (upperRadius θ) (nhdsWithin θ (Iio θ)) (nhds 0) := by
  have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hc : ContinuousAt (upperRadius θ) θ :=
    (hasDerivAt_upperRadius hs).continuousAt
  simpa [upperRadius] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- At the left endpoint the magnitude diverges to positive infinity. -/
theorem tendsto_upperRadius_nhdsGT {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (upperRadius θ) (nhdsWithin 0 (Ioi 0)) atTop := by
  have hs : Tendsto Real.sin (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with φ hφ
      exact Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have ht : Tendsto (fun φ : ℝ => θ - φ) (nhdsWithin 0 (Ioi 0)) (nhds θ) := by
    have hi : Tendsto (fun φ : ℝ => φ) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub hi
  have hr : Tendsto (fun φ : ℝ => (θ - φ) / Real.sin φ)
      (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using ht.pos_mul_atTop hθ hs.inv_tendsto_nhdsGT_zero
  have hcos : Tendsto Real.cos (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun φ : ℝ => (θ - φ) * Real.cos φ / Real.sin φ)
      (nhdsWithin 0 (Ioi 0)) atTop := by
    simpa only [div_mul_eq_mul_div] using hr.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hcos
  exact hr.atTop_mul_atTop₀ (Real.tendsto_exp_atTop.comp hu)

/-- Every positive magnitude determines exactly one angle parameter. -/
theorem existsUnique_upperRadius {θ r : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) (hr : 0 < r) :
    ∃! φ : ℝ, φ ∈ Ioo 0 θ ∧ upperRadius θ φ = r := by
  have hlo : ∀ᶠ φ in nhdsWithin θ (Iio θ), upperRadius θ φ < r :=
    (tendsto_upperRadius_nhdsLT hθ).eventually (eventually_lt_nhds hr)
  have hleft : ∀ᶠ φ in nhdsWithin θ (Iio θ), φ ∈ Ioo 0 θ := Ioo_mem_nhdsLT hθ.1
  obtain ⟨a, ha, har⟩ := (hleft.and hlo).exists
  have hhi : ∀ᶠ φ in nhdsWithin 0 (Ioi 0), r ≤ upperRadius θ φ :=
    (tendsto_upperRadius_nhdsGT hθ.1).eventually_ge_atTop r
  have hright : ∀ᶠ φ in nhdsWithin 0 (Ioi 0), φ ∈ Ioo 0 θ := Ioo_mem_nhdsGT hθ.1
  obtain ⟨b, hb, hbr⟩ := (hright.and hhi).exists
  have hc : ContinuousOn (upperRadius θ) (Ioo 0 θ) := by
    intro φ hφ
    exact (hasDerivAt_upperRadius
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hθ.2)))).continuousAt.continuousWithinAt
  obtain ⟨φ, hφ, he⟩ := isPreconnected_Ioo.intermediate_value ha hb hc ⟨har.le, hbr⟩
  refine ⟨φ, ⟨hφ, he⟩, ?_⟩
  intro ψ hψ
  exact upperRadius_injOn hθ.2 hψ.1 hφ (hψ.2.trans he.symm)

/-- A positive magnitude and an upper-half-plane angle have a principal-region preimage. -/
theorem exists_principalRange_mulExp_polar {θ r : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (hr : 0 < r) :
    ∃ w : ℂ, w ∈ principalRange ∧
      (mulExp w).re = r * Real.cos θ ∧ (mulExp w).im = r * Real.sin θ := by
  obtain ⟨φ, ⟨hφ, he⟩, _⟩ := existsUnique_upperRadius hθ hr
  have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hθ.2))
  refine ⟨upperCandidate θ φ, upperCandidate_mem_principalRange hθ hφ, ?_, ?_⟩
  · rw [mulExp_upperCandidate_re hs, he]
  · rw [mulExp_upperCandidate_im hs, he]

/-- Every upper-half-plane input has a preimage in the principal output region. -/
theorem exists_principalRange_mulExp_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, w ∈ principalRange ∧ mulExp w = z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have ha : 0 < z.arg := by
    have hn := Complex.arg_nonneg_iff.mpr hz.le
    by_contra h
    have he : z.arg = 0 := le_antisymm (not_lt.mp h) hn
    have hs := Complex.norm_mul_sin_arg z
    simp [he] at hs
    linarith
  have hb : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz))
  obtain ⟨w, hw, hre, him⟩ := exists_principalRange_mulExp_polar
    ⟨ha, hb⟩ (norm_pos_iff.mpr hz0)
  refine ⟨w, hw, Complex.ext ?_ ?_⟩
  · exact hre.trans (Complex.norm_mul_cos_arg z)
  · exact him.trans (Complex.norm_mul_sin_arg z)

/-- Existence on the entire principal slit domain, using conjugation and the real branch. -/
theorem mulExp_surjOn_principalDomain : Set.SurjOn mulExp principalRange principalDomain := by
  intro z hz
  rcases lt_trichotomy z.im 0 with hi | hi | hi
  · obtain ⟨w, hw, he⟩ := exists_principalRange_mulExp_of_im_pos
      (z := starRingEnd ℂ z) (by simpa using hi)
    refine ⟨starRingEnd ℂ w, (conj_mem_principalRange w).mpr hw, ?_⟩
    rw [mulExp_conj, he]
    simp
  · have hr : -Real.exp (-1) < z.re := by simpa [principalDomain, hi] using hz
    have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [heq]
    exact (existsUnique_principalRange_mulExp_ofReal hr).exists
  · exact exists_principalRange_mulExp_of_im_pos hi

end LambertW.Complex
