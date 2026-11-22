module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Tactic

/-!
# Shared ingredients of Cardano's formula

For `x^3 + p*x + q = 0`, put `A = -q/2 + sqrt(D)` and `B = -q/2 - sqrt(D)`,
where `D = q^2/4 + p^3/27`. This file defines the discriminant and the two
radicands, the primitive cube root of unity `omega`, and the three Cardano
values `pairedRoots s t` of any pair of cube roots. If `s^3 + t^3 = -q` and
`s * t = -p/3`, those three values are exactly the roots of the depressed
cubic, by an exact factorization. It also defines the depressed coefficients
of a general cubic and the shift relating the two.

Every Cardano formula in `CardanoComplex` and `CardanoReal` is built on these.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open Complex
open scoped ComplexConjugate

def discriminant (p q : ℂ) : ℂ := q ^ 2 / 4 + p ^ 3 / 27

def radicandPlus (p q : ℂ) : ℂ := -q / 2 + Complex.sqrt (discriminant p q)

def radicandMinus (p q : ℂ) : ℂ := -q / 2 - Complex.sqrt (discriminant p q)

@[simp] theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide)

theorem radicands_sum (p q : ℂ) : radicandPlus p q + radicandMinus p q = -q := by
  unfold radicandPlus radicandMinus
  ring

theorem radicands_product (p q : ℂ) :
    radicandPlus p q * radicandMinus p q = (-p / 3) ^ 3 := by
  unfold radicandPlus radicandMinus
  have h := sqrt_sq (discriminant p q)
  unfold discriminant at h ⊢
  linear_combination -h

/-- A primitive cube root of unity, `(-1 + i*sqrt(3))/2`. -/
def omega : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2

theorem omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold omega
  calc
    _ = ((Real.sqrt 3 : ℂ) ^ 2 * I ^ 2 + 3) / 4 := by ring
    _ = 0 := by rw [hs, I_sq]; norm_num

theorem omega_sq : omega ^ 2 = -omega - 1 := by linear_combination omega_quadratic

@[simp] theorem omega_cube : omega ^ 3 = 1 := by
  linear_combination (omega - 1) * omega_quadratic

theorem omega_conj : conj omega = omega ^ 2 := by
  rw [omega_sq]
  simp only [omega, map_div₀, map_add, map_neg, map_one, map_mul, conj_ofReal,
    conj_I, show conj (2 : ℂ) = 2 from conj_ofReal 2]
  ring

/-- The algebraic identity underlying all three Cardano roots. -/
theorem factorization_identity (x s t : ℂ) :
    (x - (s + t)) * (x - (omega * s + omega ^ 2 * t)) *
      (x - (omega ^ 2 * s + omega * t)) =
        x ^ 3 - 3 * (s * t) * x - (s ^ 3 + t ^ 3) := by
  simp only [omega_sq]
  ring_nf
  rw [omega_sq]
  ring

/-- The three Cardano values for any compatible pair of cube roots. -/
def pairedRoots (s t : ℂ) : List ℂ :=
  [s + t, omega * s + omega ^ 2 * t, omega ^ 2 * s + omega * t]

theorem mem_pairedRoots_iff {p q s t x : ℂ}
    (hsum : s ^ 3 + t ^ 3 = -q) (hprod : s * t = -p / 3) :
    x ∈ pairedRoots s t ↔ x ^ 3 + p * x + q = 0 := by
  have hfactor := factorization_identity x s t
  rw [hsum, hprod] at hfactor
  have hpoly : (x - (s + t)) * (x - (omega * s + omega ^ 2 * t)) *
      (x - (omega ^ 2 * s + omega * t)) = x ^ 3 + p * x + q := by
    linear_combination hfactor
  rw [← hpoly]
  simp [pairedRoots, mul_eq_zero, sub_eq_zero, or_assoc]

/-- Coefficients after dividing by `a` and removing the quadratic term. -/
def depressedP (a b c : ℂ) : ℂ := c / a - (b / a) ^ 2 / 3

def depressedQ (a b c d : ℂ) : ℂ :=
  2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a

theorem depressed_shift (a b c d x : ℂ) :
    (x + (b / a) / 3) ^ 3 + depressedP a b c * (x + (b / a) / 3) +
      depressedQ a b c d = x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a := by
  unfold depressedP depressedQ
  ring

end CubicEquation.CardanoComplex
