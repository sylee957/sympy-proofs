module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import SympyProofs.CubicEquation.CardanoComplex.Basic

/-!
# Monic cubic and quadratic polynomials and their multisets of roots

`monicCubic a b c` is the polynomial `X^3 + a*X^2 + b*X + c` and
`monicQuadratic a b` is `X^2 + a*X + b`, both over the complex numbers. The
`roots` of a polynomial is a multiset, so it records each root with its
multiplicity.

`monicCubic_roots_of_forall_eq` turns a factorization into linear factors,
checked at every point, into the multiset of roots.
`monicQuadratic_roots_eq_pair_iff` characterizes the two roots of the quadratic
by their sum and product, and `monicQuadratic_roots` is the quadratic formula.
`mem_roots_monicCubic` and `mem_roots_monicQuadratic` say that the members of
these multisets are exactly the solutions of the equations.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open Complex

section Polynomials

open Polynomial

/-- The monic cubic polynomial `X^3 + a*X^2 + b*X + c`. -/
def monicCubic (a b c : ℂ) : ℂ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c

@[simp] theorem eval_monicCubic (a b c x : ℂ) :
    (monicCubic a b c).eval x = x ^ 3 + a * x ^ 2 + b * x + c := by
  simp [monicCubic]

theorem monicCubic_ne_zero (a b c : ℂ) : monicCubic a b c ≠ 0 := by
  intro h
  have h3 := congrArg (fun p : ℂ[X] => p.coeff 3) h
  simp [monicCubic, coeff_X_pow] at h3

/-- The members of the multiset of roots are the solutions of the equation. -/
theorem mem_roots_monicCubic (a b c x : ℂ) :
    x ∈ (monicCubic a b c).roots ↔ x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
  rw [mem_roots (monicCubic_ne_zero a b c), IsRoot, eval_monicCubic]

/-- If the cubic equals `(x - r₁) * (x - r₂) * (x - r₃)` at every point, its
roots with multiplicity are `r₁`, `r₂`, `r₃`. -/
theorem monicCubic_roots_of_forall_eq {a b c r₁ r₂ r₃ : ℂ}
    (h : ∀ x : ℂ, x ^ 3 + a * x ^ 2 + b * x + c = (x - r₁) * (x - r₂) * (x - r₃)) :
    (monicCubic a b c).roots = {r₁, r₂, r₃} := by
  have hpoly : monicCubic a b c =
      (({r₁, r₂, r₃} : Multiset ℂ).map fun r => X - C r).prod := by
    refine Polynomial.funext fun x => ?_
    simp [h x, mul_assoc]
  rw [hpoly, roots_multiset_prod_X_sub_C]

/-- The monic quadratic polynomial `X^2 + a*X + b`. -/
def monicQuadratic (a b : ℂ) : ℂ[X] := X ^ 2 + C a * X + C b

@[simp] theorem eval_monicQuadratic (a b x : ℂ) :
    (monicQuadratic a b).eval x = x ^ 2 + a * x + b := by
  simp [monicQuadratic]

theorem monicQuadratic_ne_zero (a b : ℂ) : monicQuadratic a b ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) h
  simp [monicQuadratic, coeff_X_pow] at h2

/-- The members of the multiset of roots are the solutions of the equation. -/
theorem mem_roots_monicQuadratic (a b x : ℂ) :
    x ∈ (monicQuadratic a b).roots ↔ x ^ 2 + a * x + b = 0 := by
  rw [mem_roots (monicQuadratic_ne_zero a b), IsRoot, eval_monicQuadratic]

/-- The roots of `X^2 + a*X + b` with multiplicity are `x₁`, `x₂` exactly when
their sum is `-a` and their product is `b`. -/
theorem monicQuadratic_roots_eq_pair_iff {a b x₁ x₂ : ℂ} :
    (monicQuadratic a b).roots = {x₁, x₂} ↔ x₁ + x₂ = -a ∧ x₁ * x₂ = b := by
  have h := roots_quadratic_eq_pair_iff_of_ne_zero (a := (1 : ℂ)) (b := a) (c := b)
    (x1 := x₁) (x2 := x₂) one_ne_zero
  rw [show C (1 : ℂ) * X ^ 2 + C a * X + C b = monicQuadratic a b by simp [monicQuadratic]] at h
  rw [h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, by linear_combination -h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, by linear_combination -h2⟩

end Polynomials

/-- The quadratic formula: the roots of `X^2 + a*X + b`. -/
theorem monicQuadratic_roots (a b : ℂ) :
    (monicQuadratic a b).roots =
      {(-a - Complex.sqrt (a ^ 2 - 4 * b)) / 2, (-a + Complex.sqrt (a ^ 2 - 4 * b)) / 2} :=
  monicQuadratic_roots_eq_pair_iff.mpr
    ⟨by ring, by linear_combination (-1 / 4 : ℂ) * sqrt_sq (a ^ 2 - 4 * b)⟩

/-- The roots of `Y^2 + p` are the two square roots of `-p`. -/
theorem monicQuadratic_roots_pure (p : ℂ) :
    (monicQuadratic 0 p).roots = {-Complex.sqrt (-p), Complex.sqrt (-p)} :=
  monicQuadratic_roots_eq_pair_iff.mpr
    ⟨by ring, by linear_combination (-1 : ℂ) * sqrt_sq (-p)⟩

end CubicEquation.CardanoComplex
