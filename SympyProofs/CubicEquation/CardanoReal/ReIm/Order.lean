module

public import SympyProofs.CubicEquation.CardanoReal.ReIm.Formula
public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Order

/-!
# Which root each field of `modifiedPrincipalCubicRootsReIm` holds

Write `Δ` for `cubicDiscriminant a b c d`, and compare with the fields of
`modifiedPrincipalCubicRoots`.

* The first fields of the two functions are always the same number.
* If `0 ≤ Δ`, the second fields agree and the third fields agree.
* If `Δ < 0`, the second and third fields are exchanged.

Consequently, if `0 < Δ` the second field has positive imaginary part and the
third is its conjugate; if `Δ = 0` the second and third fields are equal; and
if `Δ < 0` all three fields are real with `x₂ < x₁ < x₀`, a descending order.

None of these statements needs the leading coefficient to be nonzero.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-! ### The square root in the quadratic factor -/

/-- The number under the second square root is `-3` times the squared
difference of the two Cardano radicals. -/
theorem neg_three_mul_sq_sub_four_mul (p q : ℝ) :
    -3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ) =
      -3 * (modifiedU p q - modifiedV p q) ^ 2 := by
  have h1 : (principalRealRoot p q : ℂ) = modifiedU p q + modifiedV p q :=
    principalRealRoot_coe p q
  have h2 := modifiedU_mul_modifiedV p q
  linear_combination
    (-3 * ((principalRealRoot p q : ℂ) + (modifiedU p q + modifiedV p q))) * h1 - 12 * h2

private theorem sqrt_neg_three_mul_sq_ofReal {s t : ℝ} (hst : t ≤ s) :
    Complex.sqrt (-3 * ((s : ℂ) - (t : ℂ)) ^ 2) = ((Real.sqrt 3 * (s - t) : ℝ) : ℂ) * I := by
  have hx : -3 * ((s : ℂ) - (t : ℂ)) ^ 2 = ((-(3 * (s - t) ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hx, sqrt_ofReal, neg_neg,
    Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg (s - t)]),
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (sub_nonneg.mpr hst)]
  simp

private theorem sqrt_neg_three_mul_sq_sub_conj {w : ℂ} (hw : 0 ≤ w.im) :
    Complex.sqrt (-3 * (w - conj w) ^ 2) = ((2 * Real.sqrt 3 * w.im : ℝ) : ℂ) := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hx : -3 * (w - conj w) ^ 2 = (((2 * Real.sqrt 3 * w.im) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sub_conj]
    push_cast
    linear_combination (-12 * (w.im : ℂ) ^ 2) * I_sq + (-4 * (w.im : ℂ) ^ 2) * hs
  rw [hx, sqrt_ofReal, Real.sqrt_sq (mul_nonneg (by positivity) hw),
    Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (sq_nonneg _))]
  simp

/-- For nonnegative discriminant the second square root is purely imaginary. -/
theorem sqrt_quadratic_of_nonneg {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ)) =
      ((Real.sqrt 3 * (realCubicSurd (realRadicandPlus p q) -
        realCubicSurd (realRadicandMinus p q)) : ℝ) : ℂ) * I := by
  rw [neg_three_mul_sq_sub_four_mul, modifiedU_of_nonneg h, modifiedV_of_nonneg h]
  exact sqrt_neg_three_mul_sq_ofReal
    (strictMono_realCubicSurd.monotone (realRadicandMinus_le p q))

/-- For negative discriminant the second square root is a positive real. -/
theorem sqrt_quadratic_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ)) =
      ((2 * Real.sqrt 3 * (principal (upperRadicand p q)).im : ℝ) : ℂ) := by
  rw [neg_three_mul_sq_sub_four_mul, modifiedU_of_neg h, modifiedV_of_neg h]
  exact sqrt_neg_three_mul_sq_sub_conj (principal_im_pos (upperRadicand_im_pos h)).le

/-! ### Depressed coefficients: comparison with the roots-of-unity values -/

theorem quadratic_plus_of_nonneg {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    (-(principalRealRoot p q : ℂ) +
        Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ))) / 2 =
      omega * modifiedU p q + omega ^ 2 * modifiedV p q := by
  have h1 : (principalRealRoot p q : ℂ) = modifiedU p q + modifiedV p q :=
    principalRealRoot_coe p q
  rw [sqrt_quadratic_of_nonneg h, h1, modifiedU_of_nonneg h, modifiedV_of_nonneg h,
    omega_mul_ofReal_add]
  push_cast
  ring

theorem quadratic_minus_of_nonneg {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    (-(principalRealRoot p q : ℂ) -
        Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ))) / 2 =
      omega ^ 2 * modifiedU p q + omega * modifiedV p q := by
  have h1 : (principalRealRoot p q : ℂ) = modifiedU p q + modifiedV p q :=
    principalRealRoot_coe p q
  rw [sqrt_quadratic_of_nonneg h, h1, modifiedU_of_nonneg h, modifiedV_of_nonneg h,
    omega_sq_mul_ofReal_add]
  push_cast
  ring

theorem quadratic_plus_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    (-(principalRealRoot p q : ℂ) +
        Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ))) / 2 =
      omega ^ 2 * modifiedU p q + omega * modifiedV p q := by
  have h1 : (principalRealRoot p q : ℂ) = modifiedU p q + modifiedV p q :=
    principalRealRoot_coe p q
  rw [sqrt_quadratic_of_neg h, h1, omega_sq_mul_modifiedU_add_of_neg h,
    modifiedU_add_modifiedV_of_neg h]
  push_cast
  ring

theorem quadratic_minus_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    (-(principalRealRoot p q : ℂ) -
        Complex.sqrt (-3 * (principalRealRoot p q : ℂ) ^ 2 - 4 * (p : ℂ))) / 2 =
      omega * modifiedU p q + omega ^ 2 * modifiedV p q := by
  have h1 : (principalRealRoot p q : ℂ) = modifiedU p q + modifiedV p q :=
    principalRealRoot_coe p q
  rw [sqrt_quadratic_of_neg h, h1, omega_mul_modifiedU_add_of_neg h,
    modifiedU_add_modifiedV_of_neg h]
  push_cast
  ring

/-! ### The fields of `modifiedPrincipalCubicRootsReIm` -/

theorem modifiedPrincipalCubicRootsReIm_x₀_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₀ =
      principalRealRoot (realDepressedP a b c) (realDepressedQ a b c d) - b / a / 3 := by
  simp only [modifiedPrincipalCubicRootsReIm, principalRealRoot, realDepressedP,
    realDepressedQ, radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant]

theorem modifiedPrincipalCubicRootsReIm_x₁_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁ =
      (-(principalRealRoot (realDepressedP a b c) (realDepressedQ a b c d) : ℂ) +
        Complex.sqrt
          (-3 * (principalRealRoot (realDepressedP a b c) (realDepressedQ a b c d) : ℂ) ^ 2 -
            4 * (realDepressedP a b c : ℂ))) / 2 - ((b / a / 3 : ℝ) : ℂ) := by
  simp only [modifiedPrincipalCubicRootsReIm, principalRealRoot, realDepressedP,
    realDepressedQ, radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant]

theorem modifiedPrincipalCubicRootsReIm_x₂_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂ =
      (-(principalRealRoot (realDepressedP a b c) (realDepressedQ a b c d) : ℂ) -
        Complex.sqrt
          (-3 * (principalRealRoot (realDepressedP a b c) (realDepressedQ a b c d) : ℂ) ^ 2 -
            4 * (realDepressedP a b c : ℂ))) / 2 - ((b / a / 3 : ℝ) : ℂ) := by
  simp only [modifiedPrincipalCubicRootsReIm, principalRealRoot, realDepressedP,
    realDepressedQ, radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant]

/-! ### Comparison of the two functions -/

/-- The two functions return the same first solution. -/
theorem modifiedPrincipalCubicRootsReIm_x₀_coe (a b c d : ℝ) :
    ((modifiedPrincipalCubicRootsReIm a b c d).x₀ : ℂ) =
      (modifiedPrincipalCubicRoots a b c d).x₀ := by
  rw [modifiedPrincipalCubicRootsReIm_x₀_eq, modifiedPrincipalCubicRoots_x₀_eq, ofReal_sub,
    principalRealRoot_coe]
  rfl

/-- For nonnegative discriminant the two functions return the same second solution. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_of_nonneg {a b c d : ℝ}
    (h : 0 ≤ cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁ = (modifiedPrincipalCubicRoots a b c d).x₁ := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_eq, modifiedPrincipalCubicRoots_x₁_eq,
    quadratic_plus_of_nonneg h]

/-- For nonnegative discriminant the two functions return the same third solution. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_of_nonneg {a b c d : ℝ}
    (h : 0 ≤ cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂ = (modifiedPrincipalCubicRoots a b c d).x₂ := by
  rw [modifiedPrincipalCubicRootsReIm_x₂_eq, modifiedPrincipalCubicRoots_x₂_eq,
    quadratic_minus_of_nonneg h]

/-- For negative discriminant the second solution here is the third solution there. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_of_neg {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁ = (modifiedPrincipalCubicRoots a b c d).x₂ := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_eq, modifiedPrincipalCubicRoots_x₂_eq,
    quadratic_plus_of_neg h]

/-- For negative discriminant the third solution here is the second solution there. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_of_neg {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂ = (modifiedPrincipalCubicRoots a b c d).x₁ := by
  rw [modifiedPrincipalCubicRootsReIm_x₂_eq, modifiedPrincipalCubicRoots_x₁_eq,
    quadratic_minus_of_neg h]

/-! ### One real root -/

/-- For nonnegative discriminant the third solution is the conjugate of the second. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_eq_conj {a b c d : ℝ}
    (h : 0 ≤ cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂ =
      conj (modifiedPrincipalCubicRootsReIm a b c d).x₁ := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_of_nonneg h,
    modifiedPrincipalCubicRootsReIm_x₂_of_nonneg h]
  exact modifiedPrincipalCubicRoots_x₂_eq_conj h

/-- For positive discriminant the second solution lies in the upper half-plane. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_im_pos {a b c d : ℝ}
    (h : 0 < cubicDiscriminant a b c d) :
    0 < (modifiedPrincipalCubicRootsReIm a b c d).x₁.im := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_of_nonneg h.le]
  exact modifiedPrincipalCubicRoots_x₁_im_pos h

/-- For positive discriminant the third solution lies in the lower half-plane. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_im_neg {a b c d : ℝ}
    (h : 0 < cubicDiscriminant a b c d) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂.im < 0 := by
  rw [modifiedPrincipalCubicRootsReIm_x₂_of_nonneg h.le]
  exact modifiedPrincipalCubicRoots_x₂_im_neg h

/-! ### A repeated root -/

/-- For zero discriminant the second and third solutions are the same. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_eq_x₂ {a b c d : ℝ}
    (h : cubicDiscriminant a b c d = 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁ =
      (modifiedPrincipalCubicRootsReIm a b c d).x₂ := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_of_nonneg h.ge,
    modifiedPrincipalCubicRootsReIm_x₂_of_nonneg h.ge]
  exact modifiedPrincipalCubicRoots_x₁_eq_x₂ h

/-- For zero discriminant the first solution coincides with the repeated one
exactly when the depressed constant coefficient vanishes, that is, for a triple root. -/
theorem modifiedPrincipalCubicRootsReIm_x₀_eq_x₁_iff {a b c d : ℝ}
    (h : cubicDiscriminant a b c d = 0) :
    ((modifiedPrincipalCubicRootsReIm a b c d).x₀ : ℂ) =
        (modifiedPrincipalCubicRootsReIm a b c d).x₁ ↔
      realDepressedQ a b c d = 0 := by
  rw [modifiedPrincipalCubicRootsReIm_x₀_coe, modifiedPrincipalCubicRootsReIm_x₁_of_nonneg h.ge]
  exact modifiedPrincipalCubicRoots_x₀_eq_x₁_iff h

/-! ### Three real roots -/

/-- For nonpositive discriminant the second solution is real. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_im {a b c d : ℝ}
    (h : cubicDiscriminant a b c d ≤ 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁.im = 0 := by
  rcases h.lt_or_eq with hlt | heq
  · rw [modifiedPrincipalCubicRootsReIm_x₁_of_neg hlt]
    exact modifiedPrincipalCubicRoots_x₂_im h
  · rw [modifiedPrincipalCubicRootsReIm_x₁_of_nonneg heq.ge]
    exact modifiedPrincipalCubicRoots_x₁_im h

/-- For nonpositive discriminant the third solution is real. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_im {a b c d : ℝ}
    (h : cubicDiscriminant a b c d ≤ 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂.im = 0 := by
  rcases h.lt_or_eq with hlt | heq
  · rw [modifiedPrincipalCubicRootsReIm_x₂_of_neg hlt]
    exact modifiedPrincipalCubicRoots_x₁_im h
  · rw [modifiedPrincipalCubicRootsReIm_x₂_of_nonneg heq.ge]
    exact modifiedPrincipalCubicRoots_x₂_im h

/-- For negative discriminant the third solution is below the second. -/
theorem modifiedPrincipalCubicRootsReIm_x₂_re_lt_x₁_re {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₂.re <
      (modifiedPrincipalCubicRootsReIm a b c d).x₁.re := by
  rw [modifiedPrincipalCubicRootsReIm_x₁_of_neg h, modifiedPrincipalCubicRootsReIm_x₂_of_neg h]
  exact modifiedPrincipalCubicRoots_x₁_re_lt_x₂_re h

/-- For negative discriminant the second solution is below the first. -/
theorem modifiedPrincipalCubicRootsReIm_x₁_re_lt_x₀ {a b c d : ℝ}
    (h : cubicDiscriminant a b c d < 0) :
    (modifiedPrincipalCubicRootsReIm a b c d).x₁.re <
      (modifiedPrincipalCubicRootsReIm a b c d).x₀ := by
  have h0 := modifiedPrincipalCubicRoots_x₂_re_lt_x₀_re h
  rw [← modifiedPrincipalCubicRootsReIm_x₀_coe, ofReal_re] at h0
  rw [modifiedPrincipalCubicRootsReIm_x₁_of_neg h]
  exact h0

end CubicEquation.CardanoReal
