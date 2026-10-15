import SympyProofs.LambertW.Complex.Branches.Log
import SympyProofs.LambertW.Complex.Boundary.Internal.MinusOne.LowerEndpoint
import SympyProofs.LambertW.Complex.Principal.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Logarithmic characterization of indexed W₋₁ -/
namespace LambertW.Complex
open Set Filter Topology

/-- Index -1 differs from the principal branch on the slit plane. -/
theorem minusOne_ne_principal {z : ℂ} (hz : z ∈ branchDomain) :
    branch (-1) z ≠ principal z := branch_negSucc_ne_principal 0 hz

theorem im_minusOne_ne_zero {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (-1) z).im ≠ 0 := im_branch_negSucc_ne_zero 0 hz

/-- Index -1 takes values in the lower half-plane. -/
theorem im_minusOne_neg {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (-1) z).im < 0 := im_branch_negSucc_neg 0 hz

/-- The logarithmic lift selecting index -1. -/
noncomputable def minusOneLogInput (z : ℂ) : ℂ := Complex.log z - 2 * Real.pi * Complex.I

/-- The general logarithmic equation specialized to index -1. -/
theorem minusOne_add_log {z : ℂ} (hz : z ∈ branchDomain) :
    branch (-1) z + Complex.log (branch (-1) z) = minusOneLogInput z := by
  simpa [negativeBranchLogInput, minusOneLogInput] using branch_negSucc_add_log 0 hz

/-- The curved strip selecting the indexed negative branch. -/
def minusOneRange : Set ℂ :=
  {w | w.im < 0 ∧ -3 * Real.pi < w.im + Complex.arg w ∧
    w.im + Complex.arg w < -Real.pi}

theorem minusOne_mem_range {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (-1)) z ∈ minusOneRange := by
  have he := congrArg Complex.im (minusOne_add_log hz)
  simp [minusOneLogInput, Complex.mul_im, Complex.log_im] at he
  have ha := Complex.neg_pi_lt_arg z
  have hb := lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)
  refine ⟨im_minusOne_neg hz, ?_, ?_⟩ <;> linarith

/-- In particular the branch lies in a strip of height `3π`. -/
theorem neg_three_pi_lt_im_minusOne {z : ℂ} (hz : z ∈ branchDomain) :
    -3 * Real.pi < ((branch (-1)) z).im := by
  have hr := (minusOne_mem_range hz).2.1
  have ha := Complex.arg_neg_iff.mpr (im_minusOne_neg hz)
  linarith

/-- Exact residual for the first logarithmic approximation. -/
theorem minusOne_sub_logInput {z : ℂ} (hz : z ∈ branchDomain) :
    (branch (-1)) z - minusOneLogInput z = -Complex.log ((branch (-1)) z) := by
  have := minusOne_add_log hz
  linear_combination this

/-- A quantitative residual estimate, without asymptotic notation. -/
theorem norm_minusOne_sub_logInput_le {z : ℂ} (hz : z ∈ branchDomain) :
    ‖(branch (-1)) z - minusOneLogInput z‖ ≤ |Real.log ‖(branch (-1)) z‖| + Real.pi := by
  rw [minusOne_sub_logInput hz, norm_neg]
  have hb := Complex.norm_le_abs_re_add_abs_im (Complex.log ((branch (-1)) z))
  simp only [Complex.log_re, Complex.log_im] at hb
  have ha : |Complex.arg ((branch (-1)) z)| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  linarith

/-- The indexed branch stays outside the closed unit disk. -/
theorem one_lt_norm_minusOne {z : ℂ} (hz : z ∈ branchDomain) :
    1 < ‖(branch (-1)) z‖ := by
  by_contra hn
  have hr : ‖(branch (-1)) z‖ ≤ 1 := le_of_not_gt hn
  have hi := im_minusOne_neg hz
  have ha := Complex.neg_pi_lt_arg ((branch (-1)) z)
  have hs := Real.sin_le (show 0 ≤ Complex.arg ((branch (-1)) z) + Real.pi by linarith)
  rw [Real.sin_add_pi] at hs
  have he := Complex.norm_mul_sin_arg ((branch (-1)) z)
  have hnpos : 0 < ‖(branch (-1)) z‖ := norm_pos_iff.mpr (by
    intro h; simp [h] at hi)
  have hsin : Real.sin (Complex.arg ((branch (-1)) z)) < 0 := by nlinarith
  have hb := (minusOne_mem_range hz).2.2
  nlinarith [mul_le_mul_of_nonpos_right hr hsin.le]

/-- An explicit upper bound in terms of the input modulus alone. -/
theorem norm_minusOne_le_log_norm {z : ℂ} (hz : z ∈ branchDomain) :
    ‖(branch (-1)) z‖ ≤ 2 * |Real.log ‖z‖| + 6 * Real.pi := by
  have hr := one_lt_norm_minusOne hz
  have hlog : 0 ≤ Real.log ‖(branch (-1)) z‖ := Real.log_nonneg hr.le
  have hhalf : Real.log ‖(branch (-1)) z‖ ≤ ‖(branch (-1)) z‖ / 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖(branch (-1)) z‖ / 2)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he := congrArg Complex.re (minusOne_add_log hz)
  simp [minusOneLogInput, Complex.mul_re, Complex.log_re] at he
  have hn := Complex.norm_le_abs_re_add_abs_im ((branch (-1)) z)
  have hi := neg_three_pi_lt_im_minusOne hz
  rw [abs_of_neg (im_minusOne_neg hz)] at hn
  have hre : |((branch (-1)) z).re| ≤ |Real.log ‖z‖| + Real.log ‖(branch (-1)) z‖ := by
    rw [show ((branch (-1)) z).re = Real.log ‖z‖ - Real.log ‖(branch (-1)) z‖ by linarith]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hlog])
  linarith

/-- Explicit logarithmic error bound, valid throughout the slit plane.
It gives a quantitative first-order expansion at both zero and infinity. -/
theorem norm_minusOne_sub_logInput_le_explicit {z : ℂ} (hz : z ∈ branchDomain) :
    ‖(branch (-1)) z - minusOneLogInput z‖ ≤
      Real.log (2 * |Real.log ‖z‖| + 6 * Real.pi) + Real.pi := by
  have hr := one_lt_norm_minusOne hz
  have h := norm_minusOne_sub_logInput_le hz
  rw [abs_of_nonneg (Real.log_nonneg hr.le)] at h
  exact h.trans (add_le_add
    (Real.log_le_log (by linarith) (norm_minusOne_le_log_norm hz)) le_rfl)

end LambertW.Complex
