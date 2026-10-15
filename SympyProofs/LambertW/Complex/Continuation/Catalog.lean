import SympyProofs.LambertW.Complex.Boundary.Branches.Matching
import SympyProofs.LambertW.Complex.Boundary.Branches.Compatibility

/-!
# Catalog of analytic continuation across the real cut

`AnalyticCrossing upper lower x` means that a single analytic inverse near `x`
agrees with the indexed branch `upper` above the real axis and `lower` below it.
It can be traversed in either direction. This is stronger than equality of traces.

Proved entries (upper index, lower index):
* `(-(n+2), -(n+1))` for every `x < 0`, including `-1/e`;
* `(n+1, n+2)` for every `x < 0`, including `-1/e`;
* `(-1, 1)` for `-1/e < x < 0` (the middle branch);
* `(0, 0)` for `-1/e < x < 0` (the principal branch).

Remaining catalog entries: `(0, 1)` and `(-1, 0)` for `x < -1/e`.
The shared value `-1` at `x = -1/e` is critical, so the regular crossing
criterion does not apply there. See the principal and middle Puiseux results.
At zero the nonprincipal branches have no finite extension.

These are local continuation results, not yet endpoint permutations for loops.
The latter require assembling crossings into path lifts and proving monodromy.
-/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

/-- A common analytic inverse across the cut, with indices ordered upper then lower. -/
def AnalyticCrossing (upper lower : ℤ) (x : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧
    (∀ᶠ z in 𝓝 (x : ℂ), mulExp (F z) = z) ∧
    (∀ᶠ z in 𝓝[BoundarySide.upper.halfPlane] (x : ℂ), branch upper z = F z) ∧
    (∀ᶠ z in 𝓝[BoundarySide.lower.halfPlane] (x : ℂ), branch lower z = F z)

/-- Equal noncritical boundary values are restrictions of one analytic local inverse. -/
theorem analyticCrossing_of_matching {upper lower : ℤ} {x : ℝ} (hx : x < 0)
    (he : branchWithBoundary upper .upper (x : ℂ) =
      branchWithBoundary lower .lower (x : ℂ))
    (hn : branchWithBoundary upper .upper (x : ℂ) ≠ -1) :
    AnalyticCrossing upper lower x := by
  rw [branchWithBoundary_ofReal _ _ hx, branchWithBoundary_ofReal _ _ hx] at he
  rw [branchWithBoundary_ofReal _ _ hx] at hn
  obtain ⟨F, ha, hl, hr⟩ := exists_analytic_localInverse hn
  have hi := mulExp_branchBoundaryValue upper .upper hx
  rw [hi] at ha hr
  refine ⟨F, ha, hr, ?_, ?_⟩
  · filter_upwards [(tendsto_branch_boundary upper .upper hx).eventually hl,
      self_mem_nhdsWithin] with z hz hd
    rw [mulExp_branch upper (BoundarySide.upper.halfPlane_subset_branchDomain hd)] at hz
    exact hz.symm
  · have ht := tendsto_branch_boundary lower .lower hx
    rw [← he] at ht
    filter_upwards [ht.eventually hl, self_mem_nhdsWithin] with z hz hd
    rw [mulExp_branch lower (BoundarySide.lower.halfPlane_subset_branchDomain hd)] at hz
    exact hz.symm

/-- Away from the critical input, equality of finite boundary values suffices. -/
theorem analyticCrossing_of_matching_of_ne_branchPoint {upper lower : ℤ} {x : ℝ}
    (hx : x < 0) (hxb : x ≠ -Real.exp (-1))
    (he : branchWithBoundary upper .upper (x : ℂ) =
      branchWithBoundary lower .lower (x : ℂ)) : AnalyticCrossing upper lower x := by
  apply analyticCrossing_of_matching hx he
  intro hw
  have hi := mulExp_branchWithBoundary upper .upper
    (show (x : ℂ) ≠ 0 by exact_mod_cast ne_of_lt hx)
  rw [hw, mulExp_neg_one] at hi
  apply hxb
  have hh := congrArg Complex.re hi
  simpa [Complex.exp_re] using hh.symm

/-- All adjacent negative sheets join regularly, even above the critical input. -/
theorem analyticCrossing_negative (n : ℕ) {x : ℝ} (hx : x < 0) :
    AnalyticCrossing (Int.negSucc (n + 1)) (Int.negSucc n) x := by
  apply analyticCrossing_of_matching hx
    (branchWithBoundary_negSucc_succ_upper_eq_lower n hx)
  rw [branchWithBoundary_negSucc_succ_upper_eq_lower n hx,
    branchWithBoundary_ofReal _ _ hx]
  intro he
  have hi := im_branchBoundaryValue_negSucc_lower_neg n hx
  rw [he] at hi
  simp at hi

/-- All adjacent positive sheets join regularly, even above the critical input. -/
theorem analyticCrossing_positive (n : ℕ) {x : ℝ} (hx : x < 0) :
    AnalyticCrossing (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) x := by
  apply analyticCrossing_of_matching hx
    (branchWithBoundary_nat_add_two_lower_eq_upper n hx).symm
  rw [branchWithBoundary_ofReal _ _ hx, branchBoundaryValue_natSucc_upper n hx]
  intro he
  have hh := congrArg Complex.im he
  have hi := im_branchBoundaryValue_negSucc_lower_neg n hx
  simp at hh
  linarith

/-- The middle branch joins indices -1 above and +1 below the real lower interval. -/
theorem analyticCrossing_middle {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    AnalyticCrossing (-1) 1 x :=
  analyticCrossing_of_matching_of_ne_branchPoint hx.2 (ne_of_gt hx.1)
    (branchWithBoundary_neg_one_upper_eq_one_lower ⟨hx.1.le, hx.2⟩)

/-- The principal branch continues across this interval without changing index. -/
theorem analyticCrossing_principal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    AnalyticCrossing 0 0 x := by
  apply analyticCrossing_of_matching_of_ne_branchPoint hx.2 (ne_of_gt hx.1)
  rw [branchWithBoundary_zero_ofReal .upper hx.1.le,
    branchWithBoundary_zero_ofReal .lower hx.1.le]

end LambertW.Complex
