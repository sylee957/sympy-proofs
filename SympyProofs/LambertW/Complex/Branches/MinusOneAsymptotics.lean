import SympyProofs.LambertW.Complex.Branches.MinusOneLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Explicit two-term logarithmic approximation to W₋₁

The estimates use only the input and apply both near zero and near infinity.
All complex logarithms are principal logarithms.
-/
namespace LambertW.Complex
open Set

/-- Computable real error envelope for the first logarithmic approximation. -/
noncomputable def minusOneLogError (z : ℂ) : ℝ :=
  Real.log (2 * |Real.log ‖z‖| + 6 * Real.pi) + Real.pi

theorem im_minusOneLogInput_neg {z : ℂ} (_hz : z ∈ branchDomain) :
    (minusOneLogInput z).im < 0 := by
  have h := Complex.arg_le_pi z
  simp [minusOneLogInput, Complex.mul_im, Complex.log_im]
  linarith [Real.pi_pos]

private theorem log_div_of_im_neg {u v : ℂ} (hu : u.im < 0) (hv : v.im < 0) :
    Complex.log (u / v) = Complex.log u - Complex.log v := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have he : Complex.exp (Complex.log u - Complex.log v) = u / v := by
    rw [Complex.exp_sub, Complex.exp_log hu0, Complex.exp_log hv0]
  rw [← he]
  apply Complex.log_exp
  · simp only [Complex.sub_im, Complex.log_im]
    have := Complex.arg_neg_iff.mpr hv
    linarith [Complex.neg_pi_lt_arg u]
  · simp only [Complex.sub_im, Complex.log_im]
    have := Complex.arg_neg_iff.mpr hu
    linarith [Complex.neg_pi_lt_arg v]

/-- Explicit second-order error bound. The size condition involves only `z`,
so it can be checked without evaluating Lambert W. -/
theorem norm_minusOne_sub_twoTerm_le {z : ℂ} (hz : z ∈ branchDomain)
    (hsmall : minusOneLogError z ≤ ‖minusOneLogInput z‖ / 2) :
    ‖(branch (-1)) z - (minusOneLogInput z - Complex.log (minusOneLogInput z))‖ ≤
      (3 / 2 : ℝ) * minusOneLogError z / ‖minusOneLogInput z‖ := by
  let L := minusOneLogInput z
  have hL : L ≠ 0 := by
    intro h
    have := im_minusOneLogInput_neg hz
    change L.im < 0 at this
    simp [h] at this
  have hLp : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hb : ‖(branch (-1)) z - L‖ ≤ minusOneLogError z :=
    norm_minusOne_sub_logInput_le_explicit hz
  have hs : ‖((branch (-1)) z - L) / L‖ ≤ 1 / 2 := by
    rw [norm_div]
    apply (div_le_iff₀ hLp).mpr
    linarith
  have he : 1 + ((branch (-1)) z - L) / L = (branch (-1)) z / L := by field_simp; ring
  have hh := Complex.norm_log_one_add_half_le_self hs
  rw [he, log_div_of_im_neg (im_minusOne_neg hz) (im_minusOneLogInput_neg hz)] at hh
  have hr : (branch (-1)) z - (L - Complex.log L) =
      -(Complex.log ((branch (-1)) z) - Complex.log L) := by
    have h := minusOne_add_log hz
    change (branch (-1)) z + Complex.log ((branch (-1)) z) = L at h
    linear_combination h
  rw [hr, norm_neg]
  calc
    _ ≤ (3 / 2 : ℝ) * ‖((branch (-1)) z - L) / L‖ := hh
    _ ≤ (3 / 2 : ℝ) * (minusOneLogError z / ‖L‖) := by
      rw [norm_div]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hLp.le) (by norm_num)
    _ = _ := by ring

/-- An elementary sufficient condition for the two-term error estimate. -/
theorem minusOneLogError_le_half {z : ℂ} (h : 64 ≤ |Real.log ‖z‖|) :
    minusOneLogError z ≤ ‖minusOneLogInput z‖ / 2 := by
  let t := |Real.log ‖z‖|
  have ht : 64 ≤ t := h
  have hp := Real.pi_pos
  have hpi := Real.pi_lt_four
  have hb : 0 < 2 * t + 6 * Real.pi := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hb (by norm_num : (0:ℝ) < 16))
  rw [Real.log_div (ne_of_gt hb) (by norm_num)] at hl
  have h16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)
  have hn := Complex.abs_re_le_norm (minusOneLogInput z)
  have hre : (minusOneLogInput z).re = Real.log ‖z‖ := by
    simp [minusOneLogInput, Complex.mul_re, Complex.log_re]
  rw [hre] at hn
  change t ≤ ‖minusOneLogInput z‖ at hn
  change Real.log (2 * t + 6 * Real.pi) + Real.pi ≤ _
  linarith

/-- Explicit two-term estimate in both asymptotic regimes. -/
theorem norm_minusOne_sub_twoTerm_le_of_log_norm {z : ℂ}
    (hz : z ∈ branchDomain) (h : 64 ≤ |Real.log ‖z‖|) :
    ‖(branch (-1)) z - (minusOneLogInput z - Complex.log (minusOneLogInput z))‖ ≤
      (3 / 2 : ℝ) * minusOneLogError z / ‖minusOneLogInput z‖ :=
  norm_minusOne_sub_twoTerm_le hz (minusOneLogError_le_half h)

/-- Quantitative expansion near zero, with an explicit input radius. -/
theorem norm_minusOne_sub_twoTerm_le_near_zero {z : ℂ}
    (hz : z ∈ branchDomain) (h : ‖z‖ ≤ Real.exp (-64)) :
    ‖(branch (-1)) z - (minusOneLogInput z - Complex.log (minusOneLogInput z))‖ ≤
      (3 / 2 : ℝ) * minusOneLogError z / ‖minusOneLogInput z‖ := by
  apply norm_minusOne_sub_twoTerm_le_of_log_norm hz
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hz)
  have hl := Real.log_le_log hp h
  rw [Real.log_exp] at hl
  have := neg_le_abs (Real.log ‖z‖)
  linarith

/-- Quantitative expansion at infinity, with an explicit input threshold. -/
theorem norm_minusOne_sub_twoTerm_le_near_infty {z : ℂ}
    (hz : z ∈ branchDomain) (h : Real.exp 64 ≤ ‖z‖) :
    ‖(branch (-1)) z - (minusOneLogInput z - Complex.log (minusOneLogInput z))‖ ≤
      (3 / 2 : ℝ) * minusOneLogError z / ‖minusOneLogInput z‖ := by
  apply norm_minusOne_sub_twoTerm_le_of_log_norm hz
  have hl := Real.log_le_log (Real.exp_pos 64) h
  rw [Real.log_exp] at hl
  exact hl.trans (le_abs_self _)

end LambertW.Complex
