module

public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Properties

/-!
# The two Cardano radicals by the sign of the discriminant

For real depressed coefficients `p,q` write `Δ = q^2/4 + p^3/27` and let
`modifiedU p q`, `modifiedV p q` be the modified principal cube roots of the
two Cardano radicands.

* If `0 ≤ Δ`, both radicands are real, and the two radicals are the real cube
  roots of `-q/2 + sqrt Δ` and `-q/2 - sqrt Δ`.
* If `Δ < 0`, the first radicand is `upperRadicand p q`, in the open upper
  half-plane, and the second is its conjugate. The radicals are the principal
  cube root of the first radicand and the conjugate of that root.

`cubicDiscriminant a b c d` is `Δ` for the depressed form of a general real
cubic. The last section expresses the three fields of
`modifiedPrincipalCubicRoots` through `modifiedU` and `modifiedV`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-! ### Depressed coefficients and the discriminant -/

/-- The linear coefficient of the depressed form of a real cubic. -/
def realDepressedP (a b c : ℝ) : ℝ := c / a - (b / a) ^ 2 / 3

/-- The constant coefficient of the depressed form of a real cubic. -/
def realDepressedQ (a b c d : ℝ) : ℝ :=
  2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a

/-- Cardano's discriminant `q^2/4 + p^3/27` of the depressed form of the real
cubic `a*x^3 + b*x^2 + c*x + d`. It is positive when the cubic has one real
root and negative when it has three distinct real roots. -/
def cubicDiscriminant (a b c d : ℝ) : ℝ :=
  realDiscriminant (realDepressedP a b c) (realDepressedQ a b c d)

/-- The first Cardano radical: the modified principal cube root of `-q/2 + sqrt Δ`. -/
def modifiedU (p q : ℝ) : ℂ := modifiedPrincipal (radicandPlus (p : ℂ) q)

/-- The second Cardano radical: the modified principal cube root of `-q/2 - sqrt Δ`. -/
def modifiedV (p q : ℝ) : ℂ := modifiedPrincipal (radicandMinus (p : ℂ) q)

theorem modifiedU_mul_modifiedV (p q : ℝ) : modifiedU p q * modifiedV p q = -(p : ℂ) / 3 :=
  modifiedPrincipal_pair_product p q

/-! ### The square root of a real number -/

/-- The principal complex square root of a real number. One of the two terms is zero. -/
theorem sqrt_ofReal (x : ℝ) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) + (Real.sqrt (-x) : ℂ) * I := by
  rcases le_total 0 x with hx | hx
  · rw [Complex.sqrt_of_nonneg (by exact_mod_cast hx), ofReal_re,
      Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hx)]
    simp
  · have hx' : (x : ℂ) = -((-x : ℝ) : ℂ) := by push_cast; ring
    rw [hx', Complex.sqrt_neg_of_nonneg (by exact_mod_cast neg_nonneg.mpr hx),
      Complex.sqrt_of_nonneg (by exact_mod_cast neg_nonneg.mpr hx), ofReal_re,
      Real.sqrt_eq_zero_of_nonpos hx]
    simp [mul_comm]

/-! ### The radicands -/

/-- The real radicand `-q/2 + sqrt Δ`, where `sqrt` is the real square root. -/
def realRadicandPlus (p q : ℝ) : ℝ := -q / 2 + Real.sqrt (realDiscriminant p q)

/-- The real radicand `-q/2 - sqrt Δ`, where `sqrt` is the real square root. -/
def realRadicandMinus (p q : ℝ) : ℝ := -q / 2 - Real.sqrt (realDiscriminant p q)

/-- The radicand `-q/2 + i * sqrt (-Δ)` in the closed upper half-plane. -/
def upperRadicand (p q : ℝ) : ℂ :=
  ((-q / 2 : ℝ) : ℂ) + ((Real.sqrt (-realDiscriminant p q) : ℝ) : ℂ) * I

theorem radicandPlus_ofReal (p q : ℝ) :
    radicandPlus (p : ℂ) q =
      (realRadicandPlus p q : ℂ) + (Real.sqrt (-realDiscriminant p q) : ℂ) * I := by
  rw [radicandPlus, discriminant_ofReal, sqrt_ofReal, realRadicandPlus]
  push_cast
  ring

theorem radicandMinus_ofReal (p q : ℝ) :
    radicandMinus (p : ℂ) q =
      (realRadicandMinus p q : ℂ) - (Real.sqrt (-realDiscriminant p q) : ℂ) * I := by
  rw [radicandMinus, discriminant_ofReal, sqrt_ofReal, realRadicandMinus]
  push_cast
  ring

theorem realRadicandMinus_le (p q : ℝ) : realRadicandMinus p q ≤ realRadicandPlus p q := by
  have h := Real.sqrt_nonneg (realDiscriminant p q)
  unfold realRadicandMinus realRadicandPlus
  linarith

theorem realRadicandMinus_lt {p q : ℝ} (h : 0 < realDiscriminant p q) :
    realRadicandMinus p q < realRadicandPlus p q := by
  have h := Real.sqrt_pos.mpr h
  unfold realRadicandMinus realRadicandPlus
  linarith

theorem realRadicandMinus_eq {p q : ℝ} (h : realDiscriminant p q = 0) :
    realRadicandMinus p q = realRadicandPlus p q := by
  unfold realRadicandMinus realRadicandPlus
  rw [h, Real.sqrt_zero, add_zero, sub_zero]

@[simp] theorem upperRadicand_im (p q : ℝ) :
    (upperRadicand p q).im = Real.sqrt (-realDiscriminant p q) := by
  simp [upperRadicand]

theorem upperRadicand_im_nonneg (p q : ℝ) : 0 ≤ (upperRadicand p q).im := by
  rw [upperRadicand_im]
  exact Real.sqrt_nonneg _

theorem upperRadicand_im_pos {p q : ℝ} (h : realDiscriminant p q < 0) :
    0 < (upperRadicand p q).im := by
  rw [upperRadicand_im]
  exact Real.sqrt_pos.mpr (neg_pos.mpr h)

theorem radicandPlus_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    radicandPlus (p : ℂ) q = upperRadicand p q := by
  rw [radicandPlus_ofReal, realRadicandPlus, Real.sqrt_eq_zero_of_nonpos h.le, upperRadicand,
    add_zero]

theorem radicandMinus_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    radicandMinus (p : ℂ) q = conj (upperRadicand p q) := by
  rw [radicandMinus_ofReal, realRadicandMinus, Real.sqrt_eq_zero_of_nonpos h.le, upperRadicand,
    sub_zero]
  simp [sub_eq_add_neg, show conj (2 : ℂ) = 2 from conj_ofReal 2]

theorem realRadicandPlus_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    realRadicandPlus p q = -q / 2 := by
  rw [realRadicandPlus, h, Real.sqrt_zero, add_zero]

theorem upperRadicand_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    upperRadicand p q = ((-q / 2 : ℝ) : ℂ) := by
  rw [upperRadicand, h, neg_zero, Real.sqrt_zero]
  simp

/-! ### The two radicals -/

/-- For nonnegative discriminant the first radical is a real cube root. -/
theorem modifiedU_of_nonneg {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    modifiedU p q = (realCubicSurd (realRadicandPlus p q) : ℂ) := by
  rw [modifiedU, radicandPlus_ofReal, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr h)]
  simp

/-- For nonnegative discriminant the second radical is a real cube root. -/
theorem modifiedV_of_nonneg {p q : ℝ} (h : 0 ≤ realDiscriminant p q) :
    modifiedV p q = (realCubicSurd (realRadicandMinus p q) : ℂ) := by
  rw [modifiedV, radicandMinus_ofReal, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr h)]
  simp

/-- For negative discriminant the first radical is a principal cube root of a
point in the open upper half-plane. -/
theorem modifiedU_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    modifiedU p q = principal (upperRadicand p q) := by
  rw [modifiedU, radicandPlus_of_neg h]
  exact modifiedPrincipal_eq_principal (Or.inr (upperRadicand_im_pos h).ne')

/-- For negative discriminant the second radical is the conjugate of the first. -/
theorem modifiedV_of_neg {p q : ℝ} (h : realDiscriminant p q < 0) :
    modifiedV p q = conj (principal (upperRadicand p q)) := by
  rw [modifiedV, radicandMinus_of_neg h, modifiedPrincipal_conj,
    modifiedPrincipal_eq_principal (Or.inr (upperRadicand_im_pos h).ne')]

/-! ### Combinations with the cube root of unity -/

theorem omega_re : omega.re = -1 / 2 := by
  simp [omega]

theorem omega_im : omega.im = Real.sqrt 3 / 2 := by
  simp [omega]

/-- The second Cardano value for two real radicals. -/
theorem omega_mul_ofReal_add (s t : ℝ) :
    omega * (s : ℂ) + omega ^ 2 * (t : ℂ) =
      ((-(s + t) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 * (s - t) : ℝ) : ℂ) * I := by
  rw [omega_sq, omega]
  push_cast
  ring

/-- The third Cardano value for two real radicals. -/
theorem omega_sq_mul_ofReal_add (s t : ℝ) :
    omega ^ 2 * (s : ℂ) + omega * (t : ℂ) =
      ((-(s + t) / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 * (s - t) : ℝ) : ℂ) * I := by
  rw [omega_sq, omega]
  push_cast
  ring

/-- The second Cardano value for a conjugate pair of radicals. -/
theorem omega_mul_add_conj (w : ℂ) :
    omega * w + omega ^ 2 * conj w = ((-w.re - Real.sqrt 3 * w.im : ℝ) : ℂ) := by
  have h : omega ^ 2 * conj w = conj (omega * w) := by rw [map_mul, omega_conj]
  rw [h, Complex.add_conj, Complex.mul_re, omega_re, omega_im]
  congr 1
  ring

/-- The third Cardano value for a conjugate pair of radicals. -/
theorem omega_sq_mul_add_conj (w : ℂ) :
    omega ^ 2 * w + omega * conj w = ((-w.re + Real.sqrt 3 * w.im : ℝ) : ℂ) := by
  have h : omega ^ 2 * w = conj (omega * conj w) := by rw [map_mul, omega_conj, conj_conj]
  rw [h, add_comm, Complex.add_conj, Complex.mul_re, omega_re, omega_im, conj_re, conj_im]
  congr 1
  ring

/-! ### The fields of `modifiedPrincipalCubicRoots` -/

theorem modifiedPrincipalCubicRoots_x₀_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRoots a b c d).x₀ =
      modifiedU (realDepressedP a b c) (realDepressedQ a b c d) +
        modifiedV (realDepressedP a b c) (realDepressedQ a b c d) - ((b / a / 3 : ℝ) : ℂ) := by
  simp only [modifiedPrincipalCubicRoots, modifiedU, modifiedV, realDepressedP, realDepressedQ,
    radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant]

theorem modifiedPrincipalCubicRoots_x₁_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRoots a b c d).x₁ =
      omega * modifiedU (realDepressedP a b c) (realDepressedQ a b c d) +
        omega ^ 2 * modifiedV (realDepressedP a b c) (realDepressedQ a b c d) -
          ((b / a / 3 : ℝ) : ℂ) := by
  simp only [modifiedPrincipalCubicRoots, modifiedU, modifiedV, realDepressedP, realDepressedQ,
    radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant, omega]

theorem modifiedPrincipalCubicRoots_x₂_eq (a b c d : ℝ) :
    (modifiedPrincipalCubicRoots a b c d).x₂ =
      omega ^ 2 * modifiedU (realDepressedP a b c) (realDepressedQ a b c d) +
        omega * modifiedV (realDepressedP a b c) (realDepressedQ a b c d) -
          ((b / a / 3 : ℝ) : ℂ) := by
  simp only [modifiedPrincipalCubicRoots, modifiedU, modifiedV, realDepressedP, realDepressedQ,
    radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant, omega]

end CubicEquation.CardanoReal
