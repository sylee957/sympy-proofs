import SympyProofs.LambertW.Complex.Boundary.Branches.Definitions

/-! # Conjugation exchanges indexed boundary traces and their approach sides -/
namespace LambertW.Complex
open Set Filter Topology ComplexConjugate

/-- Opposite nonzero indices have conjugate boundary traces from opposite sides. -/
theorem branchBoundaryValue_natSucc_conj (n : ℕ) (side : BoundarySide)
    {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (Int.ofNat (n + 1)) side x =
      conj (branchBoundaryValue (Int.negSucc n) side.opposite x) := by
  apply branchBoundaryValue_eq_of_tendsto _ side hx
  have ht := (Complex.continuous_conj.tendsto
    (branchBoundaryValue (Int.negSucc n) side.opposite x)).comp
      ((tendsto_branch_boundary (Int.negSucc n) side.opposite hx).comp
        (side.tendsto_conj x))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hd := (conj_mem_branchDomain z).mpr (side.halfPlane_subset_branchDomain hz)
  simpa using (branch_natSucc_conj n hd).symm

/-- Lower traces at positive indices match conjugate upper traces at negative indices. -/
theorem branchBoundaryValue_natSucc_lower (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (Int.ofNat (n + 1)) .lower x =
      conj (branchBoundaryValue (Int.negSucc n) .upper x) :=
  branchBoundaryValue_natSucc_conj n .lower hx

/-- Upper traces at positive indices match conjugate lower traces at negative indices. -/
theorem branchBoundaryValue_natSucc_upper (n : ℕ) {x : ℝ} (hx : x < 0) :
    branchBoundaryValue (Int.ofNat (n + 1)) .upper x =
      conj (branchBoundaryValue (Int.negSucc n) .lower x) :=
  branchBoundaryValue_natSucc_conj n .upper hx

/-- Boundary-inclusive functions satisfy the same conjugation identity on the cut. -/
theorem branchWithBoundary_natSucc_conj_ofReal (n : ℕ) (side : BoundarySide)
    {x : ℝ} (hx : x < 0) :
    branchWithBoundary (Int.ofNat (n + 1)) side (x : ℂ) =
      conj (branchWithBoundary (Int.negSucc n) side.opposite (x : ℂ)) := by
  rw [branchWithBoundary_ofReal _ _ hx, branchWithBoundary_ofReal _ _ hx]
  exact branchBoundaryValue_natSucc_conj n side hx

end LambertW.Complex
