import SympyProofs.LambertW.Complex.BranchPoint

/-!
# Uniqueness of the principal boundary extension

Agreement on the slit domain and continuity from the selected half-plane
uniquely determine every cut value. At the branch point, even one-sided
continuity suffices; a second theorem accepts ordinary continuity there.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- The open half-plane from which the chosen boundary values are approached. -/
def BoundarySide.halfPlane : BoundarySide → Set ℂ
  | .upper => {z | 0 < z.im}
  | .lower => {z | z.im < 0}

theorem BoundarySide.halfPlane_subset_principalDomain (side : BoundarySide) :
    side.halfPlane ⊆ principalDomain := by
  cases side with
  | upper => exact fun _ hz => Or.inl (ne_of_gt hz)
  | lower => exact fun _ hz => Or.inl (ne_of_lt hz)

/-- Every real point is approached by points in either open half-plane.
This ensures uniqueness of the corresponding limits is not vacuous. -/
theorem BoundarySide.nhdsWithin_halfPlane_neBot (side : BoundarySide) (x : ℝ) :
    NeBot (𝓝[side.halfPlane] (x : ℂ)) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  cases side with
  | upper =>
    have hp : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝[BoundarySide.upper.halfPlane] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (tendsto_const_nhds (x := (x : ℂ))).add (ht.mul_const Complex.I)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [BoundarySide.halfPlane] using ht
    exact hp.neBot
  | lower =>
    have hp : Tendsto (fun t : ℝ => (x : ℂ) - (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝[BoundarySide.lower.halfPlane] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (tendsto_const_nhds (x := (x : ℂ))).sub (ht.mul_const Complex.I)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [BoundarySide.halfPlane] using ht
    exact hp.neBot

/-- Both conventions have their assigned limits from the selected half-plane,
including at the branch point. -/
theorem continuousWithinAt_principalWithBoundary_cut (side : BoundarySide) {x : ℝ}
    (hx : x ≤ -Real.exp (-1)) :
    ContinuousWithinAt (principalWithBoundary side) side.halfPlane (x : ℂ) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    exact (continuousAt_principalWithBoundary_branchPoint side).continuousWithinAt
  · cases side <;> exact tendsto_principalWithBoundary_cut _ h

/-- One-sided continuity and agreement in the slit domain force a cut value. -/
theorem principal_boundary_value_unique (side : BoundarySide) {f : ℂ → ℂ}
    (hagree : EqOn f principal principalDomain) {x : ℝ}
    (hx : x ≤ -Real.exp (-1))
    (hc : ContinuousWithinAt f side.halfPlane (x : ℂ)) :
    f x = principalWithBoundary side x := by
  have := side.nhdsWithin_halfPlane_neBot x
  have he : f =ᶠ[𝓝[side.halfPlane] (x : ℂ)] principalWithBoundary side := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hd := side.halfPlane_subset_principalDomain hz
    rw [hagree hd, principalWithBoundary_of_mem side hd]
  exact tendsto_nhds_unique (hc.congr' he)
    (continuousWithinAt_principalWithBoundary_cut side hx)

/-- Uniqueness needs only one-sided continuity, even at the branch point. -/
theorem principal_boundary_extension_unique_of_continuousWithinAt
    (side : BoundarySide) {f : ℂ → ℂ}
    (hagree : EqOn f principal principalDomain)
    (hcut : ∀ x : ℝ, x ≤ -Real.exp (-1) →
      ContinuousWithinAt f side.halfPlane (x : ℂ)) :
    f = principalWithBoundary side := by
  funext z
  by_cases hz : z ∈ principalDomain
  · rw [hagree hz, principalWithBoundary_of_mem side hz]
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
    f = principalWithBoundary side := by
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
  refine ⟨principalWithBoundary side, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun _ hz => principalWithBoundary_of_mem side hz
  · exact fun _ hx => continuousWithinAt_principalWithBoundary_cut side hx.le
  · exact continuousAt_principalWithBoundary_branchPoint side
  · intro f hf
    exact principal_boundary_extension_unique side hf.1 hf.2.1 hf.2.2

end LambertW.Complex
