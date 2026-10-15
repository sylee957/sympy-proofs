import SympyProofs.LambertW.Complex.Boundary.Branches.Conjugation
import SympyProofs.LambertW.Complex.Branches.Log
import SympyProofs.LambertW.Complex.Branches.MinusOneRange

/-! # Matching adjacent indexed sheets across the negative real cut -/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

private noncomputable def cutLog (side : BoundarySide) (x : ℝ) : ℂ :=
  match side with
  | .upper => Real.log ‖(x : ℂ)‖ + Real.pi * Complex.I
  | .lower => Real.log ‖(x : ℂ)‖ - Real.pi * Complex.I

private theorem tendsto_log_cut (side : BoundarySide) {x : ℝ} (hx : x < 0) :
    Tendsto Complex.log (𝓝[side.halfPlane] (x : ℂ)) (𝓝 (cutLog side x)) := by
  cases side with
  | lower => exact Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hx rfl
  | upper =>
    exact (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hx rfl).mono_left
      (nhdsWithin_mono _ (show {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 ≤ z.im} from by
        intro z hz
        change 0 < z.im at hz
        change 0 ≤ z.im
        exact le_of_lt hz))

private theorem boundary_add_log (n : ℕ) (side : BoundarySide) {x : ℝ} (hx : x < 0)
    (hi : (branchBoundaryValue (Int.negSucc n) side x).im < 0) :
    branchBoundaryValue (Int.negSucc n) side x +
        Complex.log (branchBoundaryValue (Int.negSucc n) side x) =
      cutLog side x - 2 * Real.pi * (n + 1) * Complex.I := by
  let : NeBot (𝓝[side.halfPlane] (x : ℂ)) := side.nhdsWithin_halfPlane_neBot x
  have ht := tendsto_branch_boundary (Int.negSucc n) side hx
  have hl := (Complex.hasDerivAt_log (Or.inr (ne_of_lt hi))).continuousAt.tendsto.comp ht
  apply tendsto_nhds_unique (ht.add hl)
  apply ((tendsto_log_cut side hx).sub_const (2 * Real.pi * (n + 1) * Complex.I)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (branch_negSucc_add_log n (side.halfPlane_subset_branchDomain hz)).symm

theorem im_branchBoundaryValue_negSucc_lower_neg (n : ℕ) {x : ℝ} (hx : x < 0) :
    (branchBoundaryValue (Int.negSucc n) .lower x).im < 0 := by
  let : NeBot (𝓝[BoundarySide.lower.halfPlane] (x : ℂ)) :=
    BoundarySide.lower.nhdsWithin_halfPlane_neBot x
  have ht := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_branch_boundary (Int.negSucc n) .lower hx)
  have hb : (branchBoundaryValue (Int.negSucc n) .lower x).im ≤ -Real.pi := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (im_branch_negSucc_lt_neg_pi_of_im_neg n hz).le
  linarith [Real.pi_pos]

private theorem upper_trace_succ_im_neg (n : ℕ) {x : ℝ} (hx : x < 0) :
    (branchBoundaryValue (Int.negSucc (n + 1)) .upper x).im < 0 := by
  let : NeBot (𝓝[BoundarySide.upper.halfPlane] (x : ℂ)) :=
    BoundarySide.upper.nhdsWithin_halfPlane_neBot x
  have ht := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_branch_boundary (Int.negSucc (n + 1)) .upper hx)
  have hb : (branchBoundaryValue (Int.negSucc (n + 1)) .upper x).im ≤ -(2 * Real.pi) := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (im_branch_negSucc_succ_lt_neg_two_pi_of_im_pos n hz).le
  linarith [Real.pi_pos]

/-- The upper trace of index `-(n+2)` is the lower trace of index `-(n+1)`. -/
theorem branchBoundaryValue_negSucc_succ_upper_eq_lower (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (Int.negSucc (n + 1)) .upper x =
      branchBoundaryValue (Int.negSucc n) .lower x := by
  apply injOn_add_log_lower (upper_trace_succ_im_neg n hx) (im_branchBoundaryValue_negSucc_lower_neg n hx)
  dsimp only
  rw [boundary_add_log (n + 1) .upper hx (upper_trace_succ_im_neg n hx),
    boundary_add_log n .lower hx (im_branchBoundaryValue_negSucc_lower_neg n hx)]
  simp only [cutLog, Nat.cast_add, Nat.cast_one]
  ring

/-- Conjugation gives the corresponding matching of positive adjacent indices. -/
theorem branchBoundaryValue_nat_add_two_lower_eq_upper (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (Int.ofNat (n + 2)) .lower x =
      branchBoundaryValue (Int.ofNat (n + 1)) .upper x := by
  rw [branchBoundaryValue_natSucc_lower (n + 1) hx,
    branchBoundaryValue_natSucc_upper n hx,
    branchBoundaryValue_negSucc_succ_upper_eq_lower n hx]

/-- Adjacent negative sheets match for the boundary-inclusive API. -/
theorem branchWithBoundary_negSucc_succ_upper_eq_lower (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchWithBoundary (Int.negSucc (n + 1)) .upper (x : ℂ) =
      branchWithBoundary (Int.negSucc n) .lower (x : ℂ) := by
  rw [branchWithBoundary_ofReal _ _ hx, branchWithBoundary_ofReal _ _ hx]
  exact branchBoundaryValue_negSucc_succ_upper_eq_lower n hx

/-- Adjacent positive sheets match for the boundary-inclusive API. -/
theorem branchWithBoundary_nat_add_two_lower_eq_upper (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchWithBoundary (Int.ofNat (n + 2)) .lower (x : ℂ) =
      branchWithBoundary (Int.ofNat (n + 1)) .upper (x : ℂ) := by
  rw [branchWithBoundary_ofReal _ _ hx, branchWithBoundary_ofReal _ _ hx]
  exact branchBoundaryValue_nat_add_two_lower_eq_upper n hx

end LambertW.Complex
