import SympyProofs.LambertW.Complex.Middle.Definitions

/-!
# Continuation through finite noncritical limiting values

An inverse branch extends through an endpoint whenever its limiting value is
finite and noncritical. The extension agrees with the original branch along
the approach filter. This criterion does not assume or prove that the required
limits exist along arbitrary paths.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- A local inverse through any noncritical value, compatible with every inverse
approaching that value. This is the local step used in analytic continuation. -/
theorem exists_analytic_inverse_continuation {w : ℂ} (hw : w ≠ -1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (mulExp w) ∧ g (mulExp w) = w ∧
      HasDerivAt g (Complex.exp w * (1 + w))⁻¹ (mulExp w) ∧
      (∀ᶠ z in 𝓝 (mulExp w), mulExp (g z) = z) ∧
      ∀ (F : ℂ → ℂ) (l : Filter ℂ), Tendsto F l (𝓝 w) →
        (∀ᶠ z in l, mulExp (F z) = z) → F =ᶠ[l] g := by
  let ha := analyticAt_mulExp w
  let hn := deriv_mulExp_ne_zero hw
  let g := ha.hasStrictDerivAt.localInverse mulExp (deriv mulExp w) w hn
  have hleft : ∀ᶠ v in 𝓝 w, g (mulExp v) = v :=
    ha.hasStrictDerivAt.eventually_left_inverse hn
  refine ⟨g, ha.analyticAt_localInverse hn, hleft.self_of_nhds, ?_,
    ha.hasStrictDerivAt.eventually_right_inverse hn, ?_⟩
  · simpa only [deriv_mulExp] using (ha.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  · intro F l ht hi
    filter_upwards [ht.eventually hleft, hi] with z hz he
    rw [he] at hz
    exact hz.symm

/-- Any right inverse with a finite limit at a non-branch-point endpoint has
an analytic continuation there. The approach filter must be nontrivial. -/
theorem exists_analytic_continuation_of_tendsto {F : ℂ → ℂ} {l : Filter ℂ}
    [NeBot l] {z w : ℂ} (hz : z ≠ -Complex.exp (-1))
    (hbase : Tendsto (fun y : ℂ => y) l (𝓝 z))
    (hlim : Tendsto F l (𝓝 w)) (hinv : ∀ᶠ y in l, mulExp (F y) = y) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z = w ∧
      HasDerivAt g (Complex.exp w * (1 + w))⁻¹ z ∧
      (∀ᶠ y in 𝓝 z, mulExp (g y) = y) ∧ F =ᶠ[l] g := by
  have ht := (analyticAt_mulExp w).continuousAt.tendsto.comp hlim
  have he : mulExp w = z := tendsto_nhds_unique (ht.congr' hinv) hbase
  have hw : w ≠ -1 := by
    intro hw
    rw [hw, mulExp_neg_one] at he
    exact hz he.symm
  obtain ⟨g, hg, hgw, hd, hi, hcompat⟩ := exists_analytic_inverse_continuation hw
  rw [he] at hg hgw hd hi
  exact ⟨g, hg, hgw, hd, hi, hcompat F l hlim hinv⟩

/-- The named branch-point middle inverse continues through any endpoint where
it has a finite limit, except possibly the critical value `-1/e`. -/
theorem exists_branchPointMiddle_continuation {z w : ℂ}
    [NeBot (𝓝[branchPointMiddleDomain] z)] (hz : z ≠ -Complex.exp (-1))
    (hlim : Tendsto branchPointMiddle (𝓝[branchPointMiddleDomain] z) (𝓝 w)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z = w ∧
      HasDerivAt g (Complex.exp w * (1 + w))⁻¹ z ∧
      (∀ᶠ y in 𝓝 z, mulExp (g y) = y) ∧
      branchPointMiddle =ᶠ[𝓝[branchPointMiddleDomain] z] g := by
  apply exists_analytic_continuation_of_tendsto hz
    (tendsto_id.mono_left nhdsWithin_le_nhds) hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact mulExp_branchPointMiddle hy

end LambertW.Complex
