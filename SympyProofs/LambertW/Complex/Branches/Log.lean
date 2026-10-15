import SympyProofs.LambertW.Complex.Branches.Comparison
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Logarithmic equations for all negative indexed branches -/

namespace LambertW.Complex
open Set Filter Topology

/-- The indexed branch never coincides with the principal inverse on the slit plane. -/
theorem branch_negSucc_ne_principal (n : ℕ) {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (Int.negSucc n)) z ≠ principal z := by
  intro he
  have hp : IsPreconnected branchDomain :=
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  let : PreconnectedSpace branchDomain := Subtype.preconnectedSpace hp
  have hM : Continuous (fun t : branchDomain => (branch (Int.negSucc n)) t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      ((analyticOnNhd_branch (Int.negSucc n)) _ t.property).continuousAt.comp continuous_subtype_val.continuousAt)
  have hP : Continuous (fun t : branchDomain => principal t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticAt_principal (branchDomain_subset_principalDomain t.property)).continuousAt.comp
        continuous_subtype_val.continuousAt)
  have hh := eq_of_continuous_mulExp_lifts hM hP
    (fun t => ((mulExp_branch (Int.negSucc n)) t.property).trans
      (mulExp_principal (branchDomain_subset_principalDomain t.property)).symm)
    (fun t => by rw [(mulExp_branch (Int.negSucc n)) t.property]; exact branchDomain_ne_criticalValue t.property)
    (t₀ := ⟨z, hz⟩) he
  have hb := congrArg Complex.im (congrFun hh ⟨((branchRadius n : ℝ) : ℂ), (negativeBranchSeed n).mem_domain⟩)
  change ((branch (Int.negSucc n)) ((branchRadius n : ℝ) : ℂ)).im = (principal ((branchRadius n : ℝ) : ℂ)).im at hb
  rw [branch_negSucc_base] at hb
  have hr : -Real.exp (-1) < branchRadius n := by
    linarith [Real.exp_pos (-1), branchRadius_pos n]
  rw [principal_ofReal hr, Complex.ofReal_im] at hb
  have hn : (negativeBranchValue n).im < 0 := by
    simpa [negativeBranchValue] using neg_neg_of_pos (branchRadius_pos n)
  exact (ne_of_lt hn) hb

theorem im_branch_negSucc_ne_zero (n : ℕ) {z : ℂ} (hz : z ∈ branchDomain) :
    ((branch (Int.negSucc n)) z).im ≠ 0 := by
  intro hi
  have hw : (branch (Int.negSucc n)) z = (((branch (Int.negSucc n)) z).re : ℂ) := by apply Complex.ext <;> simp [hi]
  have he := (mulExp_branch (Int.negSucc n)) hz
  rw [hw, mulExp_ofReal] at he
  have hp : 0 < Real.mulExp ((branch (Int.negSucc n)) z).re :=
    Complex.ofReal_mem_slitPlane.mp (he.symm ▸ hz)
  have hr : 0 < ((branch (Int.negSucc n)) z).re := by
    change 0 < ((branch (Int.negSucc n)) z).re * Real.exp ((branch (Int.negSucc n)) z).re at hp
    exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hp
  apply branch_negSucc_ne_principal n hz
  apply eq_principal_of_mulExp_eq _ ((mulExp_branch (Int.negSucc n)) hz)
  rw [hw, ofReal_mem_principalRange]
  linarith

/-- All negative indexed branch values on the slit plane lie in the lower half-plane. -/
theorem im_branch_negSucc_neg (n : ℕ) {z : ℂ} (hz : z ∈ branchDomain) : ((branch (Int.negSucc n)) z).im < 0 := by
  by_contra hn
  have hp : IsPreconnected branchDomain :=
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hc : ContinuousOn (fun z => ((branch (Int.negSucc n)) z).im) branchDomain := by
    intro y hy
    exact (Complex.continuous_im.continuousAt.comp
      ((analyticOnNhd_branch (Int.negSucc n)) _ hy).continuousAt).continuousWithinAt
  have hb : ((branch (Int.negSucc n)) ((branchRadius n : ℝ) : ℂ)).im ≤ 0 := by
    rw [branch_negSucc_base]; simpa [negativeBranchValue] using (neg_nonpos.mpr (branchRadius_pos n).le)
  obtain ⟨y, hy, he⟩ := hp.intermediate_value (negativeBranchSeed n).mem_domain hz hc ⟨hb, le_of_not_gt hn⟩
  exact im_branch_negSucc_ne_zero n hy he

/-- The logarithmic lift selecting index `-(n + 1)`. -/
noncomputable def negativeBranchLogInput (n : ℕ) (z : ℂ) : ℂ := Complex.log z - 2 * Real.pi * (n + 1) * Complex.I

/-- Exact logarithmic equation with principal complex logarithms. -/
theorem branch_negSucc_add_log (n : ℕ) {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (Int.negSucc n)) z + Complex.log ((branch (Int.negSucc n)) z) = negativeBranchLogInput n z := by
  let F : ℂ → ℂ := fun z => (branch (Int.negSucc n)) z + Complex.log ((branch (Int.negSucc n)) z)
  have hder (z : ℂ) (hz : z ∈ branchDomain) : HasDerivAt F z⁻¹ z := by
    have hw : (branch (Int.negSucc n)) z ≠ 0 := by intro he; have := im_branch_negSucc_neg n hz; simp [he] at this
    have hw1 : 1 + (branch (Int.negSucc n)) z ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      exact im_branch_negSucc_ne_zero n hz hi
    have hd := ((hasDerivAt_branch (Int.negSucc n)) hz).add
      ((Complex.hasDerivAt_log (Or.inr (ne_of_lt (im_branch_negSucc_neg n hz)))).comp z
        ((hasDerivAt_branch (Int.negSucc n)) hz))
    convert hd using 1
    · rfl
    conv_lhs => rw [← (mulExp_branch (Int.negSucc n)) hz]
    unfold mulExp
    field_simp
    ring
  have hG (z : ℂ) (hz : z ∈ branchDomain) : HasDerivAt (negativeBranchLogInput n) z⁻¹ z :=
    (Complex.hasDerivAt_log hz).sub_const _
  have hp : IsPreconnected branchDomain :=
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hbase : F ((branchRadius n : ℝ) : ℂ) = negativeBranchLogInput n ((branchRadius n : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [F, branch_negSucc_base, Complex.add_re, Complex.log_re, negativeBranchLogInput,
        Complex.sub_re]
      simp [negativeBranchValue, abs_of_pos (branchRadius_pos n)]
    · have ha : Complex.arg (negativeBranchValue n) = -(Real.pi / 2) := by
        apply Complex.arg_eq_neg_pi_div_two_iff.mpr
        constructor
        · simp [negativeBranchValue, branchRadius, Complex.mul_re]
        · simpa [negativeBranchValue] using (neg_neg_of_pos (branchRadius_pos n))
      change ((branch (Int.negSucc n)) ((branchRadius n : ℝ) : ℂ) + Complex.log ((branch (Int.negSucc n)) ((branchRadius n : ℝ) : ℂ))).im =
        (Complex.log ((branchRadius n : ℝ) : ℂ) - 2 * Real.pi * (n + 1) * Complex.I).im
      rw [branch_negSucc_base, Complex.add_im, Complex.sub_im, Complex.log_im, ha]
      have hbarg : Complex.arg ((branchRadius n : ℝ) : ℂ) = 0 :=
        Complex.arg_ofReal_of_nonneg (branchRadius_pos n).le
      rw [Complex.log_im, hbarg]
      simp [negativeBranchValue, branchRadius, Complex.mul_im]
      ring
  exact Complex.isOpen_slitPlane.eqOn_of_deriv_eq hp
    (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hder z hz).deriv.trans (hG z hz).deriv.symm)
    (negativeBranchSeed n).mem_domain hbase hz


end LambertW.Complex
