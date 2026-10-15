import SympyProofs.LambertW.Complex.Branches.Comparison
import SympyProofs.LambertW.Complex.Branches.Conjugation
import SympyProofs.LambertW.Complex.Boundary.Internal.MinusOne.Lower
import SympyProofs.LambertW.Complex.Boundary.Internal.Principal.Uniqueness

/-! # One-sided limits for all indexed branches -/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

theorem BoundarySide.halfPlane_subset_branchDomain (side : BoundarySide) :
    side.halfPlane ⊆ branchDomain := by
  cases side with
  | upper => exact fun _ hz => Or.inr (ne_of_gt hz)
  | lower => exact fun _ hz => Or.inr (ne_of_lt hz)

theorem BoundarySide.convex_halfPlane (side : BoundarySide) : Convex ℝ side.halfPlane := by
  cases side
  · exact convex_halfSpace_im_gt 0
  · exact convex_halfSpace_im_lt 0

private theorem branch_im_lt_barrier (k : ℤ) (side : BoundarySide) (t : ℝ)
    (hb : (branchSeed k).value.im < t)
    (hne : ∀ z ∈ side.halfPlane, (branch k z).im ≠ t)
    {z : ℂ} (hz : z ∈ side.halfPlane) : (branch k z).im < t := by
  let a : ℂ := (branchSeed k).input
  have ha : a ∈ branchDomain := (branchSeed k).mem_domain
  have hc : ContinuousAt (fun z => (branch k z).im) a :=
    Complex.continuous_im.continuousAt.comp (analyticOnNhd_branch k _ ha).continuousAt
  have hb' : (branch k a).im < t := by simpa [a, branch_at_seed] using hb
  let : NeBot (𝓝[side.halfPlane] a) := side.nhdsWithin_halfPlane_neBot _
  have hev : ∀ᶠ z in 𝓝[side.halfPlane] a, (branch k z).im < t :=
    (hc.tendsto.eventually (eventually_lt_nhds hb')).filter_mono nhdsWithin_le_nhds
  have hs : ∀ᶠ z in 𝓝[side.halfPlane] a, z ∈ side.halfPlane := self_mem_nhdsWithin
  obtain ⟨y, hy, hyt⟩ := (hs.and hev).exists
  by_contra hn
  have hcont : ContinuousOn (fun z => (branch k z).im) side.halfPlane :=
    fun z hz => (Complex.continuous_im.continuousAt.comp
      (analyticOnNhd_branch k _ (side.halfPlane_subset_branchDomain hz)).continuousAt).continuousWithinAt
  obtain ⟨v, hv, he⟩ := side.convex_halfPlane.isPreconnected.intermediate_value
    hy hz hcont ⟨hyt.le, le_of_not_gt hn⟩
  exact hne v hv he

theorem im_branch_negSucc_lt_neg_pi_of_im_neg (n : ℕ) {z : ℂ} (hz : z.im < 0) :
    (branch (Int.negSucc n) z).im < -Real.pi := by
  apply branch_im_lt_barrier (Int.negSucc n) .lower (-Real.pi) ?_ ?_ hz
  · change (negativeBranchValue n).im < -Real.pi
    simp [negativeBranchValue, branchRadius, Complex.mul_im]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  · intro y hy he
    have hi := congrArg Complex.im (mulExp_branch (Int.negSucc n) (Or.inr (ne_of_lt hy)))
    rw [mulExp_im, he] at hi
    simp only [Real.sin_neg, Real.sin_pi, neg_zero, mul_zero, Real.cos_neg,
      Real.cos_pi, mul_neg_one, neg_neg, zero_add] at hi
    change y.im < 0 at hy
    have := mul_pos (Real.exp_pos (branch (Int.negSucc n) y).re) Real.pi_pos
    linarith

theorem im_branch_negSucc_succ_lt_neg_two_pi_of_im_pos (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    (branch (Int.negSucc (n + 1)) z).im < -(2 * Real.pi) := by
  apply branch_im_lt_barrier (Int.negSucc (n + 1)) .upper (-(2 * Real.pi)) ?_ ?_ hz
  · change (negativeBranchValue (n + 1)).im < -(2 * Real.pi)
    simp [negativeBranchValue, branchRadius, Complex.mul_im]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  · intro y hy he
    have hi := congrArg Complex.im (mulExp_branch (Int.negSucc (n + 1)) (Or.inr (ne_of_gt hy)))
    rw [mulExp_im, he] at hi
    simp only [Real.sin_neg, Real.sin_two_pi, neg_zero, mul_zero, Real.cos_neg,
      Real.cos_two_pi, mul_one, zero_add] at hi
    change 0 < y.im at hy
    have := mul_neg_of_pos_of_neg (Real.exp_pos (branch (Int.negSucc (n + 1)) y).re)
      (show -(2 * Real.pi) < 0 by linarith [Real.pi_pos])
    linarith

private theorem exists_branch_limit_of_norm_bound (k : ℤ) (side : BoundarySide)
    (hb : ∀ z ∈ side.halfPlane, 2 ≤ ‖branch k z‖) {x : ℝ} (hx : x ≠ 0) :
    ∃ w : ℂ, Tendsto (branch k) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[side.halfPlane] (x : ℂ)) := side.nhdsWithin_halfPlane_neBot x
  let δ : ℝ := ‖(x : ℂ)‖ / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (norm_pos_iff.mpr (by exact_mod_cast hx))
  let S : Set ℂ := side.halfPlane ∩ Metric.ball (x : ℂ) δ
  have hnorm : ∀ z ∈ S, δ ≤ ‖z‖ := by
    intro z hz
    have hh := norm_sub_le ((x : ℂ) - z) (-z)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    have hd : ‖(x : ℂ) - z‖ < δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
    dsimp [δ] at *
    linarith
  let C : NNReal := ⟨2 / δ, le_of_lt (div_pos (by norm_num) hδ)⟩
  have hLip : LipschitzOnWith C (branch k) S := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (analyticOnNhd_branch k _ (side.halfPlane_subset_branchDomain hz.1)).differentiableAt)
    · intro z hz
      change ‖deriv (branch k) z‖ ≤ 2 / δ
      rw [deriv_branch k (side.halfPlane_subset_branchDomain hz.1)]
      exact norm_inverse_derivative_le_of_norm_ge hδ (hnorm z hz) (hb z hz.1)
        (mulExp_branch k (side.halfPlane_subset_branchDomain hz.1))
    · exact side.convex_halfPlane.inter (convex_ball _ _)
  apply cauchy_map_iff_exists_tendsto.mp
  have hc : Cauchy (𝓝[side.halfPlane] (x : ℂ)) := cauchy_nhds.mono nhdsWithin_le_nhds
  apply hc.map_of_le hLip.uniformContinuousOn
  apply Filter.le_principal_iff.mpr
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ z in 𝓝 (x : ℂ), z ∈ Metric.ball (x : ℂ) δ from
      Metric.ball_mem_nhds (x : ℂ) hδ).filter_mono nhdsWithin_le_nhds] with z hz hb
  exact ⟨hz, hb⟩

private theorem exists_negative_branch_side_limit (n : ℕ) (side : BoundarySide)
    {x : ℝ} (hx : x < 0) :
    ∃ w : ℂ, Tendsto (branch (Int.negSucc n)) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 w) := by
  cases side with
  | lower =>
    apply exists_branch_limit_of_norm_bound _ .lower ?_ (ne_of_lt hx)
    intro z hz
    have hi := im_branch_negSucc_lt_neg_pi_of_im_neg n hz
    have hn := Complex.abs_im_le_norm (branch (Int.negSucc n) z)
    rw [abs_of_neg (by linarith [Real.pi_pos])] at hn
    linarith [Real.pi_gt_three]
  | upper =>
    cases n with
    | zero =>
      obtain ⟨w, hw, _⟩ := existsUnique_minusOne_upper_limit hx
      exact ⟨w, hw⟩
    | succ n =>
      apply exists_branch_limit_of_norm_bound _ .upper ?_ (ne_of_lt hx)
      intro z hz
      have hi := im_branch_negSucc_succ_lt_neg_two_pi_of_im_pos n hz
      have hn := Complex.abs_im_le_norm (branch (Int.negSucc (n + 1)) z)
      rw [abs_of_neg (by linarith [Real.pi_pos])] at hn
      linarith [Real.pi_gt_three]

theorem BoundarySide.tendsto_conj (side : BoundarySide) (x : ℝ) :
    Tendsto conj (𝓝[side.halfPlane] (x : ℂ)) (𝓝[side.opposite.halfPlane] (x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (Complex.continuous_conj.tendsto (x : ℂ)).mono_left
      (show 𝓝[side.halfPlane] (x : ℂ) ≤ 𝓝 (x : ℂ) from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    cases side <;> simpa [BoundarySide.halfPlane, BoundarySide.opposite] using hz

/-- Every indexed branch has a finite limit from either side at every negative real input,
including the branch point `-1/e`. -/
theorem exists_branch_side_limit (k : ℤ) (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    ∃ w : ℂ, Tendsto (branch k) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 w) := by
  cases k with
  | negSucc n => exact exists_negative_branch_side_limit n side hx
  | ofNat n =>
    cases n with
    | zero =>
      refine ⟨BoundaryInternal.principalModel side x, ?_⟩
      have ht : Tendsto (BoundaryInternal.principalModel side) (𝓝[side.halfPlane] (x : ℂ))
          (𝓝 (BoundaryInternal.principalModel side x)) := by
        by_cases h : x ≤ -Real.exp (-1)
        · exact BoundaryInternal.continuousWithinAt_principalModel_cut side h
        · exact (BoundaryInternal.analyticAt_principalModel side (Or.inr (lt_of_not_ge h))).continuousAt.continuousWithinAt
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [BoundaryInternal.principalModel_of_mem side (side.halfPlane_subset_principalDomain hz)]
      exact (branch_zero_eq_principal (side.halfPlane_subset_branchDomain hz)).symm
    | succ n =>
      obtain ⟨w, hw⟩ := exists_negative_branch_side_limit n side.opposite hx
      refine ⟨conj w, ?_⟩
      have ht := (Complex.continuous_conj.tendsto w).comp (hw.comp (side.tendsto_conj x))
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      have he := branch_natSucc_conj n ((conj_mem_branchDomain z).mpr
        (side.halfPlane_subset_branchDomain hz))
      simpa using he.symm

/-- The one-sided limit is unique; the approach filter is nonempty. -/
theorem existsUnique_branch_side_limit (k : ℤ) (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    ∃! w : ℂ, Tendsto (branch k) (𝓝[side.halfPlane] (x : ℂ)) (𝓝 w) := by
  let : NeBot (𝓝[side.halfPlane] (x : ℂ)) := side.nhdsWithin_halfPlane_neBot x
  obtain ⟨w, hw⟩ := exists_branch_side_limit k side hx
  exact ⟨w, hw, fun v hv => tendsto_nhds_unique hv hw⟩

end LambertW.Complex
