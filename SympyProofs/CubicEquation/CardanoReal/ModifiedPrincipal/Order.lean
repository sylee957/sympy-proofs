module

public import SympyProofs.CubicEquation.CardanoReal.Discriminant

/-!
# Which root each field of `modifiedPrincipalCubicRoots` holds

Write `Δ` for `cubicDiscriminant a b c d`. The first field is always real.

* If `0 < Δ`, the second field has positive imaginary part and the third is
  its conjugate.
* If `Δ = 0`, the second and third fields are equal and real.
* If `Δ < 0`, all three fields are real and `x₁ < x₂ < x₀`: the fields are the
  largest, the smallest and the middle root, in that order.

None of these statements needs the leading coefficient to be nonzero.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-! ### Depressed coefficients -/

/-- For nonnegative discriminant the third Cardano value is the conjugate of the second. -/
theorem omega_sq_mul_modifiedU_add_eq_conj {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    omega ^ 2 * modifiedU p q + omega * modifiedV p q =
      conj (omega * modifiedU p q + omega ^ 2 * modifiedV p q) := by
  rw [modifiedU_of_nonneg h, modifiedV_of_nonneg h, omega_mul_ofReal_add,
    omega_sq_mul_ofReal_add]
  simp [sub_eq_add_neg, show conj (2 : ℂ) = 2 from conj_ofReal 2]

/-- For positive discriminant the second Cardano value lies in the upper half-plane. -/
theorem omega_mul_modifiedU_add_im_pos {p q : ℝ} (h : 0 < realDiscriminant p q) :
    0 < (omega * modifiedU p q + omega ^ 2 * modifiedV p q).im := by
  rw [modifiedU_of_nonneg h.le, modifiedV_of_nonneg h.le, omega_mul_ofReal_add]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add]
  exact mul_pos (by positivity)
    (sub_pos.mpr (strictMono_realCubicSurd (realRadicandMinus_lt h)))

/-- For zero discriminant the second and third Cardano values coincide. -/
theorem omega_mul_modifiedU_add_eq_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    omega * modifiedU p q + omega ^ 2 * modifiedV p q =
      omega ^ 2 * modifiedU p q + omega * modifiedV p q := by
  rw [modifiedU_of_nonneg h.ge, modifiedV_of_nonneg h.ge, omega_mul_ofReal_add,
    omega_sq_mul_ofReal_add, realRadicandMinus_eq h]
  simp

/-- For negative discriminant the second Cardano value is real. -/
theorem omega_mul_modifiedU_add_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    omega * modifiedU p q + omega ^ 2 * modifiedV p q =
      ((-(principal (upperRadicand p q)).re -
        Real.sqrt 3 * (principal (upperRadicand p q)).im : ℝ) : ℂ) := by
  rw [modifiedU_of_neg h, modifiedV_of_neg h, omega_mul_add_conj]

/-- For negative discriminant the third Cardano value is real. -/
theorem omega_sq_mul_modifiedU_add_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    omega ^ 2 * modifiedU p q + omega * modifiedV p q =
      ((-(principal (upperRadicand p q)).re +
        Real.sqrt 3 * (principal (upperRadicand p q)).im : ℝ) : ℂ) := by
  rw [modifiedU_of_neg h, modifiedV_of_neg h, omega_sq_mul_add_conj]

/-- For negative discriminant the first Cardano value is twice a real part. -/
theorem modifiedU_add_modifiedV_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    modifiedU p q + modifiedV p q = ((2 * (principal (upperRadicand p q)).re : ℝ) : ℂ) := by
  rw [modifiedU_of_neg h, modifiedV_of_neg h, Complex.add_conj]

/-! ### One real root -/

/-- For nonnegative discriminant the third solution is the conjugate of the second. -/
theorem modifiedPrincipalCubicRoots_x₂_eq_conj {a b c d : ℝ}
    (h : 0 ≤ cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRoots a b c d).x₂ =
      conj (modifiedPrincipalCubicRoots a b c d).x₁ := by
  rw [modifiedPrincipalCubicRoots_x₂_eq, modifiedPrincipalCubicRoots_x₁_eq, map_sub,
    conj_ofReal, omega_sq_mul_modifiedU_add_eq_conj h]

/-- For positive discriminant the second solution lies in the upper half-plane. -/
theorem modifiedPrincipalCubicRoots_x₁_im_pos {a b c d : ℝ}
    (h : 0 < cubicDiscriminant a b c d) :
    0 < (modifiedPrincipalCubicRoots a b c d).x₁.im := by
  rw [modifiedPrincipalCubicRoots_x₁_eq, sub_im, ofReal_im, sub_zero]
  exact omega_mul_modifiedU_add_im_pos h

/-- For positive discriminant the third solution lies in the lower half-plane. -/
theorem modifiedPrincipalCubicRoots_x₂_im_neg {a b c d : ℝ}
    (h : 0 < cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRoots a b c d).x₂.im < 0 := by
  rw [modifiedPrincipalCubicRoots_x₂_eq_conj h.le, conj_im]
  exact neg_neg_of_pos (modifiedPrincipalCubicRoots_x₁_im_pos h)

/-! ### A repeated root -/

/-- For zero discriminant the second and third solutions are the same. -/
theorem modifiedPrincipalCubicRoots_x₁_eq_x₂ {a b c d : ℝ}
    (h : cubicDiscriminant a b c d = 0) :
    (modifiedPrincipalCubicRoots a b c d).x₁ = (modifiedPrincipalCubicRoots a b c d).x₂ := by
  rw [modifiedPrincipalCubicRoots_x₁_eq, modifiedPrincipalCubicRoots_x₂_eq,
    omega_mul_modifiedU_add_eq_of_eq_zero h]

/-- For zero discriminant the first solution coincides with the repeated one
exactly when the depressed constant coefficient vanishes, that is, for a triple root. -/
theorem modifiedPrincipalCubicRoots_x₀_eq_x₁_iff {a b c d : ℝ}
    (h : cubicDiscriminant a b c d = 0) :
    (modifiedPrincipalCubicRoots a b c d).x₀ = (modifiedPrincipalCubicRoots a b c d).x₁ ↔
      realDepressedQ a b c d = 0 := by
  rw [modifiedPrincipalCubicRoots_x₀_eq, modifiedPrincipalCubicRoots_x₁_eq, sub_left_inj,
    modifiedU_of_nonneg h.ge, modifiedV_of_nonneg h.ge, omega_mul_ofReal_add,
    realRadicandMinus_eq h, realRadicandPlus_of_eq_zero h]
  constructor
  · intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero] at hre
    have hs : realCubicSurd (-realDepressedQ a b c d / 2) = 0 := by linarith
    have hcube := realCubicSurd_cube (-realDepressedQ a b c d / 2)
    rw [hs] at hcube
    norm_num at hcube
    linarith
  · intro hQ
    rw [hQ]
    simp

/-! ### Three real roots -/

/-- For nonpositive discriminant the second solution is real. -/
theorem modifiedPrincipalCubicRoots_x₁_im {a b c d : ℝ}
    (h : cubicDiscriminant a b c d ≤ 0) :
    (modifiedPrincipalCubicRoots a b c d).x₁.im = 0 := by
  rcases h.lt_or_eq with hlt | heq
  · rw [modifiedPrincipalCubicRoots_x₁_eq, omega_mul_modifiedU_add_of_neg hlt, sub_im,
      ofReal_im, ofReal_im, sub_zero]
  · have h1 := modifiedPrincipalCubicRoots_x₂_eq_conj heq.ge
    rw [← modifiedPrincipalCubicRoots_x₁_eq_x₂ heq] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm

/-- For nonpositive discriminant the third solution is real. -/
theorem modifiedPrincipalCubicRoots_x₂_im {a b c d : ℝ}
    (h : cubicDiscriminant a b c d ≤ 0) :
    (modifiedPrincipalCubicRoots a b c d).x₂.im = 0 := by
  rcases h.lt_or_eq with hlt | heq
  · rw [modifiedPrincipalCubicRoots_x₂_eq, omega_sq_mul_modifiedU_add_of_neg hlt, sub_im,
      ofReal_im, ofReal_im, sub_zero]
  · rw [← modifiedPrincipalCubicRoots_x₁_eq_x₂ heq]
    exact modifiedPrincipalCubicRoots_x₁_im heq.le

/-- For negative discriminant the second solution is below the third. -/
theorem modifiedPrincipalCubicRoots_x₁_re_lt_x₂_re {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRoots a b c d).x₁.re < (modifiedPrincipalCubicRoots a b c d).x₂.re := by
  have hy := principal_im_pos (upperRadicand_im_pos h)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [modifiedPrincipalCubicRoots_x₁_eq, modifiedPrincipalCubicRoots_x₂_eq,
    omega_mul_modifiedU_add_of_neg h, omega_sq_mul_modifiedU_add_of_neg h, sub_re, sub_re,
    ofReal_re, ofReal_re, ofReal_re]
  nlinarith [mul_pos h3 hy]

/-- For negative discriminant the third solution is below the first. -/
theorem modifiedPrincipalCubicRoots_x₂_re_lt_x₀_re {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRoots a b c d).x₂.re < (modifiedPrincipalCubicRoots a b c d).x₀.re := by
  have hlt := principal_im_lt_sqrt_three_mul_re (upperRadicand_im_pos h)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h4 : Real.sqrt 3 * (principal (upperRadicand (realDepressedP a b c)
      (realDepressedQ a b c d))).im <
      3 * (principal (upperRadicand (realDepressedP a b c) (realDepressedQ a b c d))).re := by
    have h5 := mul_lt_mul_of_pos_left hlt h3
    rwa [← mul_assoc, hsq] at h5
  rw [modifiedPrincipalCubicRoots_x₂_eq, modifiedPrincipalCubicRoots_x₀_eq,
    omega_sq_mul_modifiedU_add_of_neg h, modifiedU_add_modifiedV_of_neg h, sub_re, sub_re,
    ofReal_re, ofReal_re, ofReal_re]
  linarith

end CubicEquation.CardanoReal
