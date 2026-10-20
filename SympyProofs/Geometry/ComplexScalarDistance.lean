module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Sign
public import Mathlib.Tactic

/-!
# Minimizing a complex residual along a real parameter

For `a c : ℂ`, the squared residual `‖a + t * c‖ ^ 2` is a real quadratic.
Its linear coefficient is determined by `re (conj a * c)`. The denominator
`‖c‖ ^ 2 + 1 - sign (‖c‖ ^ 2)` is strictly positive, even at `c = 0`.
Clamping the unconstrained minimizing parameter gives the ray and segment
minima. No nonzero-slope hypothesis or conditional appears in the formulas.
-/

@[expose] public section

namespace SympyGeometry

/-- A strictly positive denominator, equal to `‖c‖ ^ 2` for nonzero `c`. -/
noncomputable def complexSlopeDenom (c : ℂ) : ℝ :=
  ‖c‖ ^ 2 + 1 - Real.sign (‖c‖ ^ 2)

/-- An unconstrained real minimizing parameter for a complex residual. -/
noncomputable def complexLineParam (a c : ℂ) : ℝ :=
  -(star a * c).re / complexSlopeDenom c

/-- The minimizing ray parameter. -/
noncomputable def complexRayParam (a c : ℂ) : ℝ := max 0 (complexLineParam a c)

/-- The minimizing segment parameter. -/
noncomputable def complexSegmentParam (a c : ℂ) : ℝ :=
  min 1 (max 0 (complexLineParam a c))

@[simp] theorem complexSlopeDenom_zero : complexSlopeDenom 0 = 1 := by
  simp [complexSlopeDenom]

theorem complexSlopeDenom_of_ne_zero (c : ℂ) (hc : c ≠ 0) :
    complexSlopeDenom c = ‖c‖ ^ 2 := by
  have hpos : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  simp [complexSlopeDenom, Real.sign_of_pos hpos]

theorem complexSlopeDenom_pos (c : ℂ) : 0 < complexSlopeDenom c := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [complexSlopeDenom_of_ne_zero c hc]
    exact sq_pos_of_pos (norm_pos_iff.mpr hc)

@[simp] theorem complexLineParam_zero (a : ℂ) : complexLineParam a 0 = 0 := by
  simp [complexLineParam]

/-- The first-order equation holds even at zero slope, where both sides vanish. -/
theorem complexLineParam_mul_norm_sq (a c : ℂ) :
    complexLineParam a c * ‖c‖ ^ 2 = -(star a * c).re := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [complexLineParam, complexSlopeDenom_of_ne_zero c hc,
      div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]

/-- Expansion of the squared norm as a real quadratic. -/
theorem complexResidual_sq (a c : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * c‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * t * (star a * c).re + t ^ 2 * ‖c‖ ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Completing the square compares any two parameters without dividing by the slope. -/
theorem complexResidual_sq_sub (a c : ℂ) (s t : ℝ) :
    ‖a + (t : ℂ) * c‖ ^ 2 - ‖a + (s : ℂ) * c‖ ^ 2 =
      ‖c‖ ^ 2 * ((t - complexLineParam a c) ^ 2 -
        (s - complexLineParam a c) ^ 2) := by
  have hb : (star a * c).re = -(complexLineParam a c * ‖c‖ ^ 2) := by
    linarith [complexLineParam_mul_norm_sq a c]
  rw [complexResidual_sq, complexResidual_sq, hb]
  ring

theorem complexResidual_le_of_sq_le (a c : ℂ) (s t : ℝ)
    (h : (s - complexLineParam a c) ^ 2 ≤ (t - complexLineParam a c) ^ 2) :
    ‖a + (s : ℂ) * c‖ ≤ ‖a + (t : ℂ) * c‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp := mul_nonneg (sq_nonneg ‖c‖) (sub_nonneg.mpr h)
  rw [← complexResidual_sq_sub a c s t] at hp
  linarith

/-- The unconstrained parameter attains the global minimum on the real line. -/
theorem complexLineParam_le (a c : ℂ) (t : ℝ) :
    ‖a + (complexLineParam a c : ℂ) * c‖ ≤ ‖a + (t : ℂ) * c‖ := by
  apply complexResidual_le_of_sq_le
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0)]
  exact sq_nonneg _

theorem complexRayParam_nonneg (a c : ℂ) : 0 ≤ complexRayParam a c :=
  le_max_left _ _

/-- Clamping the parameter below at zero attains the ray minimum. -/
theorem complexRayParam_le (a c : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖a + (complexRayParam a c : ℂ) * c‖ ≤ ‖a + (t : ℂ) * c‖ := by
  apply complexResidual_le_of_sq_le
  by_cases hu : 0 ≤ complexLineParam a c
  · simp [complexRayParam, max_eq_right hu, sq_nonneg]
  · have hu' : complexLineParam a c ≤ 0 := le_of_not_ge hu
    rw [complexRayParam, max_eq_left hu']
    nlinarith [mul_nonneg ht (neg_nonneg.mpr hu')]

theorem complexSegmentParam_mem (a c : ℂ) :
    complexSegmentParam a c ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- Clamping to `[0, 1]` attains the segment minimum. -/
theorem complexSegmentParam_le (a c : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖a + (complexSegmentParam a c : ℂ) * c‖ ≤ ‖a + (t : ℂ) * c‖ := by
  apply complexResidual_le_of_sq_le
  by_cases hu : 0 ≤ complexLineParam a c
  · rw [complexSegmentParam, max_eq_right hu]
    by_cases hu1 : complexLineParam a c ≤ 1
    · simp [min_eq_right hu1, sq_nonneg]
    · have hu1' : 1 ≤ complexLineParam a c := le_of_not_ge hu1
      rw [min_eq_left hu1']
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
        (show 0 ≤ 2 * complexLineParam a c - t - 1 by linarith [ht.2])]
  · have hu' : complexLineParam a c ≤ 0 := le_of_not_ge hu
    simp only [complexSegmentParam, max_eq_left hu', min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith [mul_nonneg ht.1 (neg_nonneg.mpr hu')]

end SympyGeometry
