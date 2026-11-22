module

public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Order

/-!
# Simpler formulas on each sign of the discriminant

Write `Δ` for `monicCubicDiscriminant a b c`, the discriminant of the monic
cubic `x^3 + a*x^2 + b*x + c`. Once the sign of `Δ` is known,
`modifiedPrincipalMonicCubicRoots a b c` equals a simpler formula, field by
field and in the same order.

* If `0 ≤ Δ`, it equals `realRadicalMonicCubicRoots`, which takes two real cube
  roots and no complex one.
* If `Δ < 0`, it equals `singleRadicalMonicCubicRoots`, which takes one
  principal cube root.
* If `Δ = 0`, it equals `repeatedRootMonicCubicRoots`, which uses no radical.

A general cubic reduces to these by `modifiedPrincipalCubicRoots_eq_monic` and
`cubicDiscriminant_eq_monic`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-! ### Nonnegative discriminant: two real cube roots -/

/-- Cardano's formula with real cube roots for `x^3 + a*x^2 + b*x + c = 0`.
It agrees with `modifiedPrincipalMonicCubicRoots` when the discriminant is
nonnegative. -/
def realRadicalMonicCubicRoots (a b c : ℝ) : CardanoRoots :=
  let p : ℝ := b - a ^ 2 / 3
  let q : ℝ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
  let S : ℝ := realCubicSurd (-q / 2 + Real.sqrt Δ)
  let T : ℝ := realCubicSurd (-q / 2 - Real.sqrt Δ)
  let shift : ℝ := a / 3
  { x₀ := ((S + T - shift : ℝ) : ℂ)
    x₁ := ((-(S + T) / 2 - shift : ℝ) : ℂ) + ((Real.sqrt 3 / 2 * (S - T) : ℝ) : ℂ) * I
    x₂ := ((-(S + T) / 2 - shift : ℝ) : ℂ) - ((Real.sqrt 3 / 2 * (S - T) : ℝ) : ℂ) * I }

/-- For nonnegative discriminant the formula needs only real cube roots. -/
theorem modifiedPrincipalMonicCubicRoots_eq_realRadical {a b c : ℝ}
    (h : 0 ≤ monicCubicDiscriminant a b c) :
    modifiedPrincipalMonicCubicRoots a b c = realRadicalMonicCubicRoots a b c := by
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modifiedPrincipalMonicCubicRoots_x₀_eq, modifiedU_of_nonneg h, modifiedV_of_nonneg h,
      ← ofReal_add, ← ofReal_sub]
    rfl
  · rw [modifiedPrincipalMonicCubicRoots_x₁_eq, modifiedU_of_nonneg h, modifiedV_of_nonneg h,
      omega_mul_ofReal_add, add_sub_right_comm, ← ofReal_sub]
    rfl
  · rw [modifiedPrincipalMonicCubicRoots_x₂_eq, modifiedU_of_nonneg h, modifiedV_of_nonneg h,
      omega_sq_mul_ofReal_add, sub_right_comm, ← ofReal_sub]
    rfl

/-! ### Negative discriminant: one principal cube root -/

/-- Cardano's formula with one principal cube root for
`x^3 + a*x^2 + b*x + c = 0`; the conjugate of that root serves as the second
radical. It agrees with `modifiedPrincipalMonicCubicRoots` when the
discriminant is negative, where all three solutions are real. -/
def singleRadicalMonicCubicRoots (a b c : ℝ) : CardanoRoots :=
  let p : ℝ := b - a ^ 2 / 3
  let q : ℝ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
  let u := principal (-(q : ℂ) / 2 + (Real.sqrt (-Δ) : ℂ) * I)
  let shift : ℝ := a / 3
  { x₀ := ((2 * u.re - shift : ℝ) : ℂ)
    x₁ := ((-u.re - Real.sqrt 3 * u.im - shift : ℝ) : ℂ)
    x₂ := ((-u.re + Real.sqrt 3 * u.im - shift : ℝ) : ℂ) }

theorem upperRadicand_eq (p q : ℝ) :
    upperRadicand p q = -(q : ℂ) / 2 + (Real.sqrt (-realDiscriminant p q) : ℂ) * I := by
  simp [upperRadicand]

/-- For negative discriminant the formula needs only one principal cube root. -/
theorem modifiedPrincipalMonicCubicRoots_eq_singleRadical {a b c : ℝ}
    (h : monicCubicDiscriminant a b c < 0) :
    modifiedPrincipalMonicCubicRoots a b c = singleRadicalMonicCubicRoots a b c := by
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modifiedPrincipalMonicCubicRoots_x₀_eq, modifiedU_add_modifiedV_of_neg h,
      ← ofReal_sub, upperRadicand_eq]
    rfl
  · rw [modifiedPrincipalMonicCubicRoots_x₁_eq, omega_mul_modifiedU_add_of_neg h,
      ← ofReal_sub, upperRadicand_eq]
    rfl
  · rw [modifiedPrincipalMonicCubicRoots_x₂_eq, omega_sq_mul_modifiedU_add_of_neg h,
      ← ofReal_sub, upperRadicand_eq]
    rfl

/-! ### Zero discriminant: no radical -/

/-- The solutions of `x^3 + a*x^2 + b*x + c = 0` when it has a repeated root,
as rational functions of the depressed coefficients. It agrees with
`modifiedPrincipalMonicCubicRoots` when the discriminant is zero. For a triple
root `p = 0`, and the convention `x / 0 = 0` makes all three fields equal to
`-shift`, which is the triple root. -/
def repeatedRootMonicCubicRoots (a b c : ℝ) : CardanoRoots :=
  let p : ℝ := b - a ^ 2 / 3
  let q : ℝ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let shift : ℝ := a / 3
  { x₀ := ((3 * q / p - shift : ℝ) : ℂ)
    x₁ := ((-(3 * q / (2 * p)) - shift : ℝ) : ℂ)
    x₂ := ((-(3 * q / (2 * p)) - shift : ℝ) : ℂ) }

/-- For zero discriminant the real cube root of `-q/2` is `3q/(2p)`, also when `p = 0`. -/
theorem realCubicSurd_of_discriminant_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    realCubicSurd (-q / 2) = 3 * q / (2 * p) := by
  have e1 : realCubicSurd (-q / 2) ^ 3 = -q / 2 := realCubicSurd_cube _
  have e2 : realCubicSurd (-q / 2) * realCubicSurd (-q / 2) = -p / 3 := by
    have hUV := modifiedU_mul_modifiedV p q
    rw [modifiedU_of_nonneg h.ge, modifiedV_of_nonneg h.ge, realRadicandMinus_eq h,
      realRadicandPlus_of_eq_zero h] at hUV
    exact_mod_cast hUV
  by_cases hp : p = 0
  · have hs : realCubicSurd (-q / 2) = 0 := by
      apply mul_self_eq_zero.mp
      rw [e2, hp]
      simp
    rw [hs, hp]
    simp
  · rw [eq_div_iff (mul_ne_zero two_ne_zero hp)]
    linear_combination (-6) * e1 + 6 * realCubicSurd (-q / 2) * e2

/-- For zero discriminant both radicals are the rational number `3q/(2p)`. -/
theorem modifiedU_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    modifiedU p q = ((3 * q / (2 * p) : ℝ) : ℂ) := by
  rw [modifiedU_of_nonneg h.ge, realRadicandPlus_of_eq_zero h,
    realCubicSurd_of_discriminant_eq_zero h]

theorem modifiedV_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    modifiedV p q = ((3 * q / (2 * p) : ℝ) : ℂ) := by
  rw [modifiedV_of_nonneg h.ge, realRadicandMinus_eq h, realRadicandPlus_of_eq_zero h,
    realCubicSurd_of_discriminant_eq_zero h]

/-- For zero discriminant the formula needs no radical. -/
theorem modifiedPrincipalMonicCubicRoots_eq_repeatedRoot {a b c : ℝ}
    (h : monicCubicDiscriminant a b c = 0) :
    modifiedPrincipalMonicCubicRoots a b c = repeatedRootMonicCubicRoots a b c := by
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modifiedPrincipalMonicCubicRoots_x₀_eq, modifiedU_of_eq_zero h, modifiedV_of_eq_zero h,
      ← ofReal_add, ← ofReal_sub]
    change _ = ((3 * monicDepressedQ a b c / monicDepressedP a b - a / 3 : ℝ) : ℂ)
    congr 1
    ring
  · rw [modifiedPrincipalMonicCubicRoots_x₁_eq, modifiedU_of_eq_zero h, modifiedV_of_eq_zero h,
      omega_mul_ofReal_add, sub_self, mul_zero, ofReal_zero, zero_mul, add_zero, ← ofReal_sub]
    change _ = ((-(3 * monicDepressedQ a b c / (2 * monicDepressedP a b)) - a / 3 : ℝ) : ℂ)
    congr 1
    ring
  · rw [modifiedPrincipalMonicCubicRoots_x₂_eq, modifiedU_of_eq_zero h, modifiedV_of_eq_zero h,
      omega_sq_mul_ofReal_add, sub_self, mul_zero, ofReal_zero, zero_mul, sub_zero,
      ← ofReal_sub]
    change _ = ((-(3 * monicDepressedQ a b c / (2 * monicDepressedP a b)) - a / 3 : ℝ) : ℂ)
    congr 1
    ring

end CubicEquation.CardanoReal
