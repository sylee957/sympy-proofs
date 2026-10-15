import SympyProofs.LambertW.Complex.Boundary.Internal.Principal.BranchPoint

/-!
# Uniqueness of the principal boundary extension

Agreement on the slit domain and continuity from the selected half-plane
uniquely determine every cut value. At the branch point, even one-sided
continuity suffices; a second theorem accepts ordinary continuity there.
-/

namespace LambertW.Complex

open Set Filter Topology

theorem BoundarySide.halfPlane_subset_principalDomain (side : BoundarySide) :
    side.halfPlane ⊆ principalDomain := by
  cases side with
  | upper => exact fun _ hz => Or.inl (ne_of_gt hz)
  | lower => exact fun _ hz => Or.inl (ne_of_lt hz)

/-- Both conventions have their assigned limits from the selected half-plane,
including at the branch point. -/
theorem BoundaryInternal.continuousWithinAt_principalModel_cut (side : BoundarySide) {x : ℝ}
    (hx : x ≤ -Real.exp (-1)) :
    ContinuousWithinAt (BoundaryInternal.principalModel side) side.halfPlane (x : ℂ) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    exact (BoundaryInternal.continuousAt_principalModel_branchPoint side).continuousWithinAt
  · cases side <;> exact BoundaryInternal.tendsto_principalModel_cut _ h

/-- One-sided continuity and agreement in the slit domain force a cut value. -/
theorem principal_boundary_value_unique (side : BoundarySide) {f : ℂ → ℂ}
    (hagree : EqOn f principal principalDomain) {x : ℝ}
    (hx : x ≤ -Real.exp (-1))
    (hc : ContinuousWithinAt f side.halfPlane (x : ℂ)) :
    f x = BoundaryInternal.principalModel side x := by
  have := side.nhdsWithin_halfPlane_neBot x
  have he : f =ᶠ[𝓝[side.halfPlane] (x : ℂ)] BoundaryInternal.principalModel side := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hd := side.halfPlane_subset_principalDomain hz
    rw [hagree hd, BoundaryInternal.principalModel_of_mem side hd]
  exact tendsto_nhds_unique (hc.congr' he)
    (BoundaryInternal.continuousWithinAt_principalModel_cut side hx)

/-- Uniqueness needs only one-sided continuity, even at the branch point. -/
theorem principal_boundary_extension_unique_of_continuousWithinAt
    (side : BoundarySide) {f : ℂ → ℂ}
    (hagree : EqOn f principal principalDomain)
    (hcut : ∀ x : ℝ, x ≤ -Real.exp (-1) →
      ContinuousWithinAt f side.halfPlane (x : ℂ)) :
    f = BoundaryInternal.principalModel side := by
  funext z
  by_cases hz : z ∈ principalDomain
  · rw [hagree hz, BoundaryInternal.principalModel_of_mem side hz]
  · have hi : z.im = 0 := by simpa [principalDomain] using (not_or.mp hz).1
    have hr : z.re ≤ -Real.exp (-1) := le_of_not_gt (not_or.mp hz).2
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he]
    exact principal_boundary_value_unique side hagree hr (hcut z.re hr)

/-- Agreement on the slit domain, one-sided continuity on the open cut, and
ordinary continuity at the branch point characterize the entire extension. -/
theorem principal_boundary_extension_unique (side : BoundarySide) {f : ℂ → ℂ}
    (hagree : EqOn f principal principalDomain)
    (hcut : ∀ x : ℝ, x < -Real.exp (-1) →
      ContinuousWithinAt f side.halfPlane (x : ℂ))
    (hbranch : ContinuousAt f ((-Real.exp (-1) : ℝ) : ℂ)) :
    f = BoundaryInternal.principalModel side := by
  apply principal_boundary_extension_unique_of_continuousWithinAt side hagree
  intro x hx
  rcases hx.eq_or_lt with h | h
  · subst x
    exact hbranch.continuousWithinAt
  · exact hcut x h

/-- For each side, an extension with these agreement and continuity properties
exists and is unique. -/
theorem existsUnique_principal_boundary_extension (side : BoundarySide) :
    ∃! f : ℂ → ℂ, EqOn f principal principalDomain ∧
      (∀ x : ℝ, x < -Real.exp (-1) → ContinuousWithinAt f side.halfPlane (x : ℂ)) ∧
      ContinuousAt f ((-Real.exp (-1) : ℝ) : ℂ) := by
  refine ⟨BoundaryInternal.principalModel side, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun _ hz => BoundaryInternal.principalModel_of_mem side hz
  · exact fun _ hx => BoundaryInternal.continuousWithinAt_principalModel_cut side hx.le
  · exact BoundaryInternal.continuousAt_principalModel_branchPoint side
  · intro f hf
    exact principal_boundary_extension_unique side hf.1 hf.2.1 hf.2.2

end LambertW.Complex
