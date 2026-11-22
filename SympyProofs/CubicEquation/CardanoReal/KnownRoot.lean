module

public import SympyProofs.CubicEquation.CardanoReal.Basic

/-!
# Solving a cubic from one known root

If `r` is a root of the depressed cubic `x^3 + p*x + q`, factoring out `x - r`
gives the other two roots as `(-r ± sqrt(-3*r^2 - 4*p)) / 2`. The
factorization is exact, so no distinctness or nonzero-root assumption is
needed, and `p,q,r` are allowed to be complex. For a real cubic with nonzero
leading coefficient and a real root of its depressed form, shifting back gives
all three solutions.

These statements do not depend on how the root was obtained.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- Given any root, the remaining quadratic gives an exact factorization.
No distinctness or nonzero-root assumption is needed. -/
theorem depressed_factorization_of_root {p q r : ℂ}
    (hr : r ^ 3 + p * r + q = 0) (x : ℂ) :
    (x - r) * (x - (-r + Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2) *
      (x - (-r - Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2) =
        x ^ 3 + p * x + q := by
  have hs := sqrt_sq (-3 * r ^ 2 - 4 * p)
  linear_combination -(x - r) / 4 * hs - hr

/-- A known root and the two quadratic expressions give precisely all solutions. -/
theorem depressed_roots_iff_of_root {p q r : ℂ}
    (hr : r ^ 3 + p * r + q = 0) (x : ℂ) :
    x ^ 3 + p * x + q = 0 ↔ x = r ∨
      x = (-r + Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2 ∨
      x = (-r - Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2 := by
  rw [← depressed_factorization_of_root hr x]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

/-- Shift a real depressed root and its quadratic companions back to the original cubic. -/
theorem cubic_roots_iff_of_real_depressed_root {a : ℝ} (ha : a ≠ 0)
    (b c d r : ℝ)
    (hr : r ^ 3 + (c / a - (b / a) ^ 2 / 3) * r +
      (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a) = 0) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let t := Complex.sqrt (-3 * (r : ℂ) ^ 2 - 4 * (p : ℂ))
    let shift : ℝ := (b / a) / 3
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = (r : ℂ) - shift ∨
      x = (-(r : ℂ) + t) / 2 - shift ∨
      x = (-(r : ℂ) - t) / 2 - shift := by
  dsimp only
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let shift : ℝ := (b / a) / 3
  have hr' : (r : ℂ) ^ 3 + (p : ℂ) * r + q = 0 := by exact_mod_cast hr
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hscale : (a : ℂ) *
      (x ^ 3 + ((b : ℂ) / a) * x ^ 2 + ((c : ℂ) / a) * x + (d : ℂ) / a) =
      (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d := by
    field_simp
  have hshift : (shift : ℂ) = ((b : ℂ) / a) / 3 := by
    simp [shift]
  have hnorm : (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      (x + (shift : ℂ)) ^ 3 + (p : ℂ) * (x + (shift : ℂ)) + q = 0 := by
    rw [show (p : ℂ) = depressedP (a : ℂ) b c from (depressedP_ofReal a b c).symm,
      show (q : ℂ) = depressedQ (a : ℂ) b c d from (depressedQ_ofReal a b c d).symm,
      hshift, depressed_shift, ← hscale, mul_eq_zero]
    simp [ha']
  rw [hnorm, depressed_roots_iff_of_root hr']
  simp only [eq_sub_iff_add_eq]
  rfl

end CubicEquation.CardanoReal
