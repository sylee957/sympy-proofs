import SympyProofs.LambertW.Complex.Branches.MiddleComparison
import SympyProofs.LambertW.Complex.Middle.CutLimits

/-! # Upper boundary values of the indexed branch W₋₁

The boundary convention in this file is approach from the upper half-plane.
It does not identify the lower-side limits of the indexed branch.
-/
namespace LambertW.Complex
open Set Filter Topology

/-- Transfer a limit of the double-cut branch to indexed W₋₁ from above. -/
theorem tendsto_minusOne_upper_of_middle {a w : ℂ}
    (h : Tendsto middle (𝓝[{z : ℂ | 0 < z.im}] a) (𝓝 w)) :
    Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] a) (𝓝 w) := by
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact middle_eq_branch_neg_one_of_im_pos hz

theorem tendsto_minusOne_upper_branchPoint :
    Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (-Complex.exp (-1))) (𝓝 (-1)) :=
  tendsto_minusOne_upper_of_middle tendsto_middle_upper_branchPoint

/-- Every negative real input has a unique finite upper boundary value. -/
theorem existsUnique_minusOne_upper_limit {x : ℝ} (hx : x < 0) :
    ∃! w : ℂ, Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := nhdsWithin_upper_neBot x
  have hex : ∃ w : ℂ, Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w) := by
    by_cases he : x = -Real.exp (-1)
    · subst x
      exact ⟨-1, by simpa using tendsto_minusOne_upper_branchPoint⟩
    · obtain ⟨w, _, hw⟩ := exists_middle_upper_limit (ne_of_lt hx) he
      exact ⟨w, tendsto_minusOne_upper_of_middle hw⟩
  obtain ⟨w, hw⟩ := hex
  exact ⟨w, hw, fun v hv => tendsto_nhds_unique hv hw⟩

/-- Upper boundary value at negative real inputs; unspecified elsewhere. -/
noncomputable def minusOneUpperBoundary (x : ℝ) : ℂ :=
  if hx : x < 0 then (existsUnique_minusOne_upper_limit hx).exists.choose else (branch (-1)) x

theorem tendsto_minusOne_upper_boundary {x : ℝ} (hx : x < 0) :
    Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (minusOneUpperBoundary x)) := by
  simpa [minusOneUpperBoundary, hx] using (existsUnique_minusOne_upper_limit hx).exists.choose_spec

theorem minusOneUpperBoundary_eq_of_tendsto {x : ℝ} (hx : x < 0) {w : ℂ}
    (hw : Tendsto (branch (-1)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 w)) :
    minusOneUpperBoundary x = w := by
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := nhdsWithin_upper_neBot x
  exact tendsto_nhds_unique (tendsto_minusOne_upper_boundary hx) hw

@[simp] theorem minusOneUpperBoundary_branchPoint :
    minusOneUpperBoundary (-Real.exp (-1)) = -1 := by
  apply minusOneUpperBoundary_eq_of_tendsto (neg_neg_of_pos (Real.exp_pos (-1)))
  simpa using tendsto_minusOne_upper_branchPoint

theorem minusOneUpperBoundary_ofReal {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    minusOneUpperBoundary x = (Real.lower x : ℂ) :=
  minusOneUpperBoundary_eq_of_tendsto hx.2 (tendsto_minusOne_upper_ofReal hx)

/-- Boundary values still satisfy the defining inverse equation. -/
theorem mulExp_minusOneUpperBoundary {x : ℝ} (hx : x < 0) :
    mulExp (minusOneUpperBoundary x) = (x : ℂ) := by
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := nhdsWithin_upper_neBot x
  have ht := (analyticAt_mulExp (minusOneUpperBoundary x)).continuousAt.tendsto.comp
    (tendsto_minusOne_upper_boundary hx)
  apply tendsto_nhds_unique ht
  apply (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact ((mulExp_branch (-1)) (Or.inr (ne_of_gt hz))).symm

/-- The total indexed function with upper-side values assigned on its cut. -/
noncomputable def BoundaryInternal.minusOneUpperModel (z : ℂ) : ℂ :=
  if z.im = 0 ∧ z.re < 0 then minusOneUpperBoundary z.re else (branch (-1)) z

theorem BoundaryInternal.minusOneUpperModel_eq {z : ℂ} (hz : z ∈ branchDomain) :
    BoundaryInternal.minusOneUpperModel z = (branch (-1)) z := by
  have hn : ¬(z.im = 0 ∧ z.re < 0) := by
    rintro ⟨hi, hr⟩
    rcases hz with hz | hz
    · linarith
    · exact hz hi
  simp [BoundaryInternal.minusOneUpperModel, hn]

theorem BoundaryInternal.minusOneUpperModel_ofReal {x : ℝ} (hx : x < 0) :
    BoundaryInternal.minusOneUpperModel (x : ℂ) = minusOneUpperBoundary x := by
  simp [BoundaryInternal.minusOneUpperModel, hx]

/-- Continuity from above, with the boundary point included in the domain. -/
theorem BoundaryInternal.continuousWithinAt_minusOneUpperModel {x : ℝ} (hx : x < 0) :
    ContinuousWithinAt BoundaryInternal.minusOneUpperModel
      (insert (x : ℂ) {z : ℂ | 0 < z.im}) (x : ℂ) := by
  apply continuousWithinAt_insert_self.mpr
  change Tendsto BoundaryInternal.minusOneUpperModel _ _
  rw [BoundaryInternal.minusOneUpperModel_ofReal hx]
  apply (tendsto_minusOne_upper_boundary hx).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (BoundaryInternal.minusOneUpperModel_eq (Or.inr (ne_of_gt hz))).symm

/-- Full convergent Puiseux series and cubic remainder on the upper side of -1/e. -/
theorem exists_minusOne_upper_puiseux :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (-Complex.exp (-1)),
        HasSum (fun n : ℕ => (puiseuxCoeff n : ℂ) * middleParameter z ^ n)
          ((branch (-1)) z + 1) ∧
        (branch (-1)) z = -1 + middleParameter z - middleParameter z ^ 2 / 3 +
          (11 / 72 : ℂ) * middleParameter z ^ 3 + middleParameter z ^ 4 * R (middleParameter z) := by
  obtain ⟨R, hR, he⟩ := exists_middle_complex_puiseux
  refine ⟨R, hR, ?_⟩
  have hsub : 𝓝[{z : ℂ | 0 < z.im}] (-Complex.exp (-1)) ≤
      𝓝[middleDomain] (-Complex.exp (-1)) :=
    nhdsWithin_mono _ (fun _ hz => Or.inl (ne_of_gt hz))
  filter_upwards [he.filter_mono hsub, self_mem_nhdsWithin] with z hp hz
  rwa [middle_eq_branch_neg_one_of_im_pos hz] at hp

/-- Upper-side divergence at the logarithmic singularity. -/
theorem tendsto_norm_minusOne_upper_zero :
    Tendsto (fun z => ‖(branch (-1)) z‖) (𝓝[{z : ℂ | 0 < z.im}] 0) atTop := by
  have ht := tendsto_norm_middle_zero.mono_left
    (nhdsWithin_mono (0 : ℂ) (fun _ hz => Or.inl (ne_of_gt hz)))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [middle_eq_branch_neg_one_of_im_pos hz]

/-- The boundary-assigned function satisfies the inverse equation at every
nonzero complex input, including the negative real cut. -/
theorem BoundaryInternal.mulExp_minusOneUpperModel {z : ℂ} (hz : z ≠ 0) :
    mulExp (BoundaryInternal.minusOneUpperModel z) = z := by
  by_cases hcut : z.im = 0 ∧ z.re < 0
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hcut.1]
    rw [he, BoundaryInternal.minusOneUpperModel_ofReal hcut.2]
    exact mulExp_minusOneUpperBoundary hcut.2
  · have hd : z ∈ branchDomain := by
      by_cases hi : z.im = 0
      · left
        have hn : z.re ≠ 0 := by
          intro hr
          apply hz
          apply Complex.ext <;> simp [hr, hi]
        have hnonneg : 0 ≤ z.re := le_of_not_gt (fun hr => hcut ⟨hi, hr⟩)
        exact lt_of_le_of_ne hnonneg (Ne.symm hn)
      · exact Or.inr hi
    rw [BoundaryInternal.minusOneUpperModel_eq hd]
    exact (mulExp_branch (-1)) hd

/-- On the real lower interval including its finite endpoint, the chosen
boundary convention gives the real lower function. -/
theorem BoundaryInternal.minusOneUpperModel_eq_real_lower {x : ℝ}
    (hx : x ∈ Ico (-Real.exp (-1)) 0) :
    BoundaryInternal.minusOneUpperModel (x : ℂ) = (Real.lower x : ℂ) := by
  rw [BoundaryInternal.minusOneUpperModel_ofReal hx.2]
  rcases eq_or_lt_of_le hx.1 with he | he
  · subst x
    simp
  · exact minusOneUpperBoundary_ofReal ⟨he, hx.2⟩

end LambertW.Complex
