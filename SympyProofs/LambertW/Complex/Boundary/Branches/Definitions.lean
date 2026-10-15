import SympyProofs.LambertW.Complex.Boundary.Branches.Limits

/-! # Unified boundary conventions for all indexed Lambert W branches

`branchWithBoundary k side` agrees with `branch k` on the slit plane and takes
its selected one-sided limit at every negative real input. Index zero also has
value zero at the origin. For nonzero indices the value at zero is unspecified:
there is no finite continuous extension there.
-/
namespace LambertW.Complex
open Set Filter Topology

noncomputable def branchBoundaryValue (k : ℤ) (side : BoundarySide) (x : ℝ) : ℂ :=
  if hx : x < 0 then (exists_branch_side_limit k side hx).choose else branch k x

theorem tendsto_branch_boundary (k : ℤ) (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    Tendsto (branch k) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 (branchBoundaryValue k side x)) := by
  simpa only [branchBoundaryValue, dite_eq_left hx] using (exists_branch_side_limit k side hx).choose_spec

theorem branchBoundaryValue_eq_of_tendsto (k : ℤ) (side : BoundarySide) {x : ℝ}
    (hx : x < 0) {w : ℂ}
    (hw : Tendsto (branch k) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 w)) :
    branchBoundaryValue k side x = w := by
  let : NeBot (𝓝[side.halfPlane] (x : ℂ)) := side.nhdsWithin_halfPlane_neBot x
  exact tendsto_nhds_unique (tendsto_branch_boundary k side hx) hw

theorem mulExp_branchBoundaryValue (k : ℤ) (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    mulExp (branchBoundaryValue k side x) = (x : ℂ) := by
  let : NeBot (𝓝[side.halfPlane] (x : ℂ)) := side.nhdsWithin_halfPlane_neBot x
  have ht := (analyticAt_mulExp (branchBoundaryValue k side x)).continuousAt.tendsto.comp
    (tendsto_branch_boundary k side hx)
  have hi : Tendsto (fun z : ℂ => z) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 (x : ℂ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique ht
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (mulExp_branch k (side.halfPlane_subset_branchDomain hz)).symm

/-- All indexed branches, with a uniform choice of side on the negative real cut. -/
noncomputable def branchWithBoundary (k : ℤ) (side : BoundarySide) (z : ℂ) : ℂ :=
  if k = 0 ∧ z = 0 then 0
  else if z.im = 0 ∧ z.re < 0 then branchBoundaryValue k side z.re
  else branch k z

@[simp] theorem branchWithBoundary_of_mem (k : ℤ) (side : BoundarySide) {z : ℂ}
    (hz : z ∈ branchDomain) : branchWithBoundary k side z = branch k z := by
  have hn := Complex.slitPlane_ne_zero hz
  have hc : ¬ (z.im = 0 ∧ z.re < 0) := by
    rintro ⟨hi, hr⟩
    rcases hz with h | h
    · linarith
    · exact h hi
  simp [branchWithBoundary, hn, hc]

@[simp] theorem branchWithBoundary_ofReal (k : ℤ) (side : BoundarySide) {x : ℝ}
    (hx : x < 0) : branchWithBoundary k side (x : ℂ) = branchBoundaryValue k side x := by
  have hn : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hx
  simp [branchWithBoundary, hx, hn]

@[simp] theorem branchWithBoundary_zero (side : BoundarySide) : branchWithBoundary 0 side 0 = 0 := by
  simp [branchWithBoundary]

theorem analyticAt_branchWithBoundary (k : ℤ) (side : BoundarySide) {z : ℂ}
    (hz : z ∈ branchDomain) : AnalyticAt ℂ (branchWithBoundary k side) z := by
  apply (analyticOnNhd_branch k z hz).congr
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with y hy
  exact (branchWithBoundary_of_mem k side hy).symm

/-- The selected assignment is continuous when approaching from its chosen side. -/
theorem continuousWithinAt_branchWithBoundary (k : ℤ) (side : BoundarySide) {x : ℝ}
    (hx : x < 0) : ContinuousWithinAt (branchWithBoundary k side)
      (insert (x : ℂ) side.halfPlane) (x : ℂ) := by
  rw [continuousWithinAt_insert_self]
  change Tendsto (branchWithBoundary k side) _ _
  rw [branchWithBoundary_ofReal k side hx]
  apply (tendsto_branch_boundary k side hx).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (branchWithBoundary_of_mem k side (side.halfPlane_subset_branchDomain hz)).symm

/-- The boundary assignment remains a right inverse at every nonzero input. -/
theorem mulExp_branchWithBoundary (k : ℤ) (side : BoundarySide) {z : ℂ} (hz : z ≠ 0) :
    mulExp (branchWithBoundary k side z) = z := by
  by_cases hc : z.im = 0 ∧ z.re < 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hc.1]
    rw [he, branchWithBoundary_ofReal k side hc.2, mulExp_branchBoundaryValue k side hc.2]
  · have hd : z ∈ branchDomain := by
      by_cases hi : z.im = 0
      · left
        have hn : z.re ≠ 0 := by intro h; apply hz; apply Complex.ext <;> simp [h, hi]
        have hnon : 0 ≤ z.re := le_of_not_gt (fun h => hc ⟨hi, h⟩)
        exact lt_of_le_of_ne hnon (Ne.symm hn)
      · exact Or.inr hi
    rw [branchWithBoundary_of_mem k side hd, mulExp_branch k hd]

/-- The one-sided continuity requirement uniquely determines the assigned cut value. -/
theorem branchWithBoundary_unique_at_cut (k : ℤ) (side : BoundarySide) {f : ℂ → ℂ}
    (ha : EqOn f (branch k) branchDomain) {x : ℝ} (hx : x < 0)
    (hc : ContinuousWithinAt f (insert (x : ℂ) side.halfPlane) (x : ℂ)) :
    f x = branchWithBoundary k side x := by
  rw [branchWithBoundary_ofReal k side hx]
  apply Eq.symm
  apply branchBoundaryValue_eq_of_tendsto k side hx
  rw [continuousWithinAt_insert_self] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ha (side.halfPlane_subset_branchDomain hz)

/-- Agreement in the interior and the chosen one-sided continuity uniquely determine
all nonzero values of the extended branch. -/
theorem eqOn_branchWithBoundary (k : ℤ) (side : BoundarySide) {f : ℂ → ℂ}
    (ha : EqOn f (branch k) branchDomain)
    (hc : ∀ x : ℝ, x < 0 → ContinuousWithinAt f
      (insert (x : ℂ) side.halfPlane) (x : ℂ)) :
    EqOn f (branchWithBoundary k side) {z | z ≠ 0} := by
  intro z hz
  by_cases hd : z ∈ branchDomain
  · rw [branchWithBoundary_of_mem k side hd]
    exact ha hd
  · have hi : z.im = 0 := by
      by_contra hn
      exact hd (Or.inr hn)
    have hr : z.re < 0 := by
      have hn : z.re ≠ 0 := by intro h; apply hz; apply Complex.ext <;> simp [h, hi]
      have hle : z.re ≤ 0 := le_of_not_gt (fun h => hd (Or.inl h))
      exact lt_of_le_of_ne hle hn
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he]
    exact branchWithBoundary_unique_at_cut k side ha hr (hc z.re hr)

end LambertW.Complex
