import SympyProofs.RiemannZeta.EtaExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A certified path crossing the original convergence boundary

At height `π / (2 log 2)`, the imaginary part of `2^(1-s)` is strictly
negative, so the eta denominator cannot vanish. The horizontal segment from
real part `2` to real part `1/2` therefore has a certified zeta continuation.
-/

noncomputable section
namespace RiemannZeta

open unitInterval

def crossingHeight : ℝ := Real.pi / 2 / Real.log 2

theorem etaFactor_ne_zero_on_crossingLine (x : ℝ) :
    etaFactor ((x : ℂ) + Complex.I * crossingHeight) ≠ 0 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlogC : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  have him : (((Real.log 2 : ℝ) : ℂ) *
      (1 - ((x : ℂ) + Complex.I * crossingHeight))).im = -(Real.pi / 2) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.add_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, mul_zero, add_zero]
    dsimp [crossingHeight]
    field_simp
    ring
  have hne : ((2 : ℂ) ^ (1 - ((x : ℂ) + Complex.I * crossingHeight))).im ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num),
      hlogC, Complex.exp_im, him,
      Real.sin_neg, Real.sin_pi_div_two, mul_neg_one]
    exact neg_ne_zero.mpr (Real.exp_ne_zero _)
  intro h
  have heq : (2 : ℂ) ^ (1 - ((x : ℂ) + Complex.I * crossingHeight)) = 1 :=
    (sub_eq_zero.mp h).symm
  exact hne (by rw [heq]; rfl)

/-- A horizontal path from the defining half-plane into the critical strip. -/
def crossingPath : Path ((2 : ℂ) + Complex.I * crossingHeight)
    ((1 / 2 : ℂ) + Complex.I * crossingHeight) where
  toFun t := ((2 - 3 / 2 * (t : ℝ) : ℝ) : ℂ) + Complex.I * crossingHeight
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

theorem crossingPath_mem_etaDomain (t : I) : crossingPath t ∈ etaDomain := by
  constructor
  · change 0 < (((2 - 3 / 2 * (t : ℝ) : ℝ) : ℂ) + Complex.I * crossingHeight).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have ht := t.property.2
    linarith
  · exact etaFactor_ne_zero_on_crossingLine _

/-- An actual continuation leaving `re s > 1`, obtained from the sum. -/
def crossingContinuation : Continuation crossingPath :=
  Continuation.viaEta (by norm_num [rightHalfPlane]) crossingPath_mem_etaDomain

theorem crossing_endpoint_value :
    crossingContinuation.endpoint = etaQuotient ((1 / 2 : ℂ) + Complex.I * crossingHeight) := rfl

theorem crossing_endpoint_outside_rightHalfPlane :
    ((1 / 2 : ℂ) + Complex.I * crossingHeight) ∉ rightHalfPlane := by
  norm_num [rightHalfPlane]

end RiemannZeta
