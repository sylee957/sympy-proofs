import SympyProofs.LambertW.Complex.Boundary.Branches.Definitions

/-! # Recovery of the previously proved principal and negative-index boundary values -/
namespace LambertW.Complex
open Set Filter Topology

private theorem boundary_zero_eq (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    branchBoundaryValue 0 side x = BoundaryInternal.principalModel side x := by
  apply branchBoundaryValue_eq_of_tendsto 0 side hx
  have ht : Tendsto (BoundaryInternal.principalModel side) (𝓝[side.halfPlane] (x : ℂ))
      (𝓝 (BoundaryInternal.principalModel side x)) := by
    by_cases h : x ≤ -Real.exp (-1)
    · exact BoundaryInternal.continuousWithinAt_principalModel_cut side h
    · exact (BoundaryInternal.analyticAt_principalModel side (Or.inr (lt_of_not_ge h))).continuousAt.continuousWithinAt
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [BoundaryInternal.principalModel_of_mem side (side.halfPlane_subset_principalDomain hz)]
  exact (branch_zero_eq_principal (side.halfPlane_subset_branchDomain hz)).symm

/-- Compatibility with the principal proof model, including its value at zero. -/
theorem branchWithBoundary_zero_eq_model (side : BoundarySide) (z : ℂ) :
    branchWithBoundary 0 side z = BoundaryInternal.principalModel side z := by
  by_cases hz : z = 0
  · subst z; simp
  by_cases hc : z.im = 0 ∧ z.re < 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hc.1]
    rw [he, branchWithBoundary_ofReal 0 side hc.2, boundary_zero_eq side hc.2]
  · have hd : z ∈ branchDomain := by
      by_cases hi : z.im = 0
      · left
        have hn : z.re ≠ 0 := by intro h; apply hz; apply Complex.ext <;> simp [h, hi]
        exact lt_of_le_of_ne (le_of_not_gt (fun h => hc ⟨hi, h⟩)) (Ne.symm hn)
      · exact Or.inr hi
    rw [branchWithBoundary_of_mem 0 side hd, branch_zero_eq_principal hd,
      BoundaryInternal.principalModel_of_mem side (branchDomain_subset_principalDomain hd)]

theorem branchBoundaryValue_neg_one_upper {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (-1) .upper x = minusOneUpperBoundary x := by
  apply branchBoundaryValue_eq_of_tendsto (-1) .upper hx
  exact tendsto_minusOne_upper_boundary hx

theorem branchBoundaryValue_neg_one_lower {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (-1) .lower x = minusOneLowerBoundary x := by
  apply branchBoundaryValue_eq_of_tendsto (-1) .lower hx
  exact tendsto_minusOne_lower_boundary (ne_of_lt hx)

/-- The conventional real lower values are recovered by index -1 and the upper side. -/
theorem branchWithBoundary_neg_one_upper_ofReal {x : ℝ}
    (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    branchWithBoundary (-1) .upper x = (Real.lower x : ℂ) := by
  rw [branchWithBoundary_ofReal (-1) .upper hx.2, branchBoundaryValue_neg_one_upper hx.2]
  rw [← BoundaryInternal.minusOneUpperModel_ofReal hx.2]
  exact BoundaryInternal.minusOneUpperModel_eq_real_lower hx

/-- Index zero retains the full real principal interval, independent of side. -/
theorem branchWithBoundary_zero_ofReal (side : BoundarySide) {x : ℝ}
    (hx : -Real.exp (-1) ≤ x) :
    branchWithBoundary 0 side x = (Real.principal x : ℂ) := by
  rw [branchWithBoundary_zero_eq_model]
  exact BoundaryInternal.principalModel_ofReal side hx

@[simp] theorem branchWithBoundary_zero_branchPoint (side : BoundarySide) :
    branchWithBoundary 0 side ((-Real.exp (-1) : ℝ) : ℂ) = -1 := by
  rw [branchWithBoundary_zero_eq_model, BoundaryInternal.principalModel_branchPoint]

/-- The zero-index convention is analytic on the larger principal domain as well. -/
theorem analyticAt_branchWithBoundary_zero (side : BoundarySide) {z : ℂ}
    (hz : z ∈ principalDomain) : AnalyticAt ℂ (branchWithBoundary 0 side) z := by
  have he : branchWithBoundary 0 side = BoundaryInternal.principalModel side :=
    funext (branchWithBoundary_zero_eq_model side)
  rw [he]
  exact BoundaryInternal.analyticAt_principalModel side hz

theorem continuousAt_branchWithBoundary_zero_branchPoint (side : BoundarySide) :
    ContinuousAt (branchWithBoundary 0 side) ((-Real.exp (-1) : ℝ) : ℂ) := by
  have he : branchWithBoundary 0 side = BoundaryInternal.principalModel side :=
    funext (branchWithBoundary_zero_eq_model side)
  rw [he]
  exact BoundaryInternal.continuousAt_principalModel_branchPoint side

/-- The two conventions really differ for index -1 on the whole negative cut. -/
theorem branchWithBoundary_neg_one_sides_ne {x : ℝ} (hx : x < 0) :
    branchWithBoundary (-1) .lower x ≠ branchWithBoundary (-1) .upper x := by
  rw [branchWithBoundary_ofReal (-1) .lower hx, branchWithBoundary_ofReal (-1) .upper hx,
    branchBoundaryValue_neg_one_lower hx, branchBoundaryValue_neg_one_upper hx]
  exact minusOne_lower_upper_boundary_ne hx

/-- The principal boundary convention is a right inverse even at zero. -/
theorem mulExp_branchWithBoundary_zero (side : BoundarySide) (z : ℂ) :
    mulExp (branchWithBoundary 0 side z) = z := by
  by_cases hz : z = 0
  · subst z; simp [mulExp]
  · exact mulExp_branchWithBoundary 0 side hz

/-- The two principal conventions differ precisely on the open principal cut. -/
theorem branchWithBoundary_zero_sides_ne {x : ℝ} (hx : x < -Real.exp (-1)) :
    branchWithBoundary 0 .upper x ≠ branchWithBoundary 0 .lower x := by
  rw [branchWithBoundary_zero_eq_model, branchWithBoundary_zero_eq_model]
  exact BoundaryInternal.principalModel_upper_ne_lower hx

/-- The upper convention at index -1 recovers the specialized proof model off zero. -/
theorem branchWithBoundary_neg_one_upper_eq_model {z : ℂ} (hz : z ≠ 0) :
    branchWithBoundary (-1) .upper z = BoundaryInternal.minusOneUpperModel z := by
  apply Eq.symm
  apply eqOn_branchWithBoundary (-1) .upper (f := BoundaryInternal.minusOneUpperModel) ?_ ?_ hz
  · intro y hy
    rw [BoundaryInternal.minusOneUpperModel_eq hy]
  · intro x hx
    exact BoundaryInternal.continuousWithinAt_minusOneUpperModel hx

/-- The lower convention at index -1 recovers the specialized proof model off zero. -/
theorem branchWithBoundary_neg_one_lower_eq_model {z : ℂ} (hz : z ≠ 0) :
    branchWithBoundary (-1) .lower z = BoundaryInternal.minusOneLowerModel z := by
  apply Eq.symm
  apply eqOn_branchWithBoundary (-1) .lower (f := BoundaryInternal.minusOneLowerModel) ?_ ?_ hz
  · intro y hy
    rw [BoundaryInternal.minusOneLowerModel_eq hy]
  · intro x hx
    exact BoundaryInternal.continuousWithinAt_minusOneLowerModel hx

/-- On the real interval, the middle branch agrees with the upper boundary of index -1. -/
theorem middle_eq_branchWithBoundary_neg_one_upper_ofReal {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    middle (x : ℂ) = branchWithBoundary (-1) .upper x := by
  rw [middle_ofReal hx, branchWithBoundary_neg_one_upper_ofReal ⟨hx.1.le, hx.2⟩]

/-- On the real interval, the middle branch agrees with the lower boundary of index +1. -/
theorem middle_eq_branchWithBoundary_one_lower_ofReal {x : ℝ}
    (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    middle (x : ℂ) = branchWithBoundary 1 .lower x := by
  rw [branchWithBoundary_ofReal 1 .lower hx.2]
  apply Eq.symm
  apply branchBoundaryValue_eq_of_tendsto 1 .lower hx.2
  have ht := (analyticOnNhd_middle _ (ofReal_mem_middleDomain.mpr hx)).continuousAt.tendsto
  apply (ht.mono_left (show 𝓝[BoundarySide.lower.halfPlane] (x : ℂ) ≤ 𝓝 (x : ℂ) from
    nhdsWithin_le_nhds)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact middle_eq_branch_one_of_im_neg hz

/-- The lower boundary of index +1 meets the branch point at `-1`. -/
@[simp] theorem branchWithBoundary_one_lower_branchPoint :
    branchWithBoundary 1 .lower ((-Real.exp (-1) : ℝ) : ℂ) = -1 := by
  have hx : -Real.exp (-1) < 0 := neg_neg_of_pos (Real.exp_pos _)
  rw [branchWithBoundary_ofReal 1 .lower hx]
  apply branchBoundaryValue_eq_of_tendsto 1 .lower hx
  have ht : Tendsto middle
      (𝓝[BoundarySide.lower.halfPlane] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (-1)) := by
    simpa [BoundarySide.halfPlane] using tendsto_middle_lower_branchPoint
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact middle_eq_branch_one_of_im_neg hz

/-- The lower boundary of index +1 recovers the real lower branch, including the branch point. -/
theorem branchWithBoundary_one_lower_ofReal {x : ℝ}
    (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    branchWithBoundary 1 .lower x = (Real.lower x : ℂ) := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst x
    rw [branchWithBoundary_one_lower_branchPoint, Real.lower_neg_exp_neg_one]
    simp
  · rw [← middle_eq_branchWithBoundary_one_lower_ofReal ⟨h, hx.2⟩,
      middle_ofReal ⟨h, hx.2⟩]

/-- The two indexed sheets glue across the real middle interval, including the branch point. -/
theorem branchWithBoundary_neg_one_upper_eq_one_lower {x : ℝ}
    (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    branchWithBoundary (-1) .upper x = branchWithBoundary 1 .lower x := by
  rw [branchWithBoundary_neg_one_upper_ofReal hx, branchWithBoundary_one_lower_ofReal hx]

end LambertW.Complex
