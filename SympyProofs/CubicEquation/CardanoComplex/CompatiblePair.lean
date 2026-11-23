module

public import SympyProofs.CubicEquation.CardanoComplex.MonicPolynomial
public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Shortcuts

/-!
# The roots of a monic cubic from a compatible pair of radicals

Write `p = b - a^2/3` and `q = 2*a^3/27 - a*b/3 + c` for the depressed
coefficients of `X^3 + a*X^2 + b*X + c`, and `A = -q/2 + sqrt Δ`,
`B = -q/2 - sqrt Δ` for the two radicands.

`monicCubic_roots_of_compatible_pair` is the general statement: if
`U^3 + V^3 = -q` and `U * V = -p/3`, the roots of the cubic with multiplicity
are `U + V - a/3`, `ω*U + ω^2*V - a/3` and `ω^2*U + ω*V - a/3`. Every form of
Cardano's formula is an instance of it, for its own choice of `U` and `V`.

The other statements are its instances that do not yet name a testable
condition on the coefficients:

* `p = 0` and any cube root `u` of `-q` (`monicCubic_roots_of_depressedP_eq_zero`);
* `A ≠ 0`, any cube root `u` of `A` and `v = -p / (3 * u)`
  (`monicCubic_roots_of_cube_eq_radicandPlus`), in particular the principal
  cube root (`monicCubic_roots_principalQuotient`) and the modified principal
  cube root (`monicCubic_roots_quotient`);
* `B ≠ 0`, any cube root `v` of `B` and `u = -p / (3 * v)`
  (`monicCubic_roots_of_cube_eq_radicandMinus`), in particular
  `v = -(-B)^(1/3)` (`monicCubic_roots_secondRadicandQuotient`).

The rules of a solver, with conditions that can be tested, are in `Roots.lean`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open Complex

/-- The roots of the cubic from two numbers whose cubes sum to `-q` and whose
product is `-p/3`. -/
theorem monicCubic_roots_of_compatible_pair {a b c U V : ℂ}
    (hsum : U ^ 3 + V ^ 3 = -complexMonicDepressedQ a b c)
    (hprod : U * V = -complexMonicDepressedP a b / 3) :
    (monicCubic a b c).roots =
      {U + V - a / 3, omega * U + omega ^ 2 * V - a / 3,
        omega ^ 2 * U + omega * V - a / 3} := by
  refine monicCubic_roots_of_forall_eq fun x => ?_
  rw [show (x - (U + V - a / 3)) * (x - (omega * U + omega ^ 2 * V - a / 3)) *
      (x - (omega ^ 2 * U + omega * V - a / 3)) =
        (x + a / 3 - (U + V)) * (x + a / 3 - (omega * U + omega ^ 2 * V)) *
          (x + a / 3 - (omega ^ 2 * U + omega * V)) by ring,
    factorization_identity, hprod, hsum]
  unfold complexMonicDepressedP complexMonicDepressedQ
  ring

/-- When `p = 0` and `u` is a cube root of `-q`, the roots of
`X^3 + a*X^2 + b*X + c` are `u - a/3`, `u*ω - a/3` and `u*ω^2 - a/3`. -/
theorem monicCubic_roots_of_depressedP_eq_zero {a b c u : ℂ}
    (hp : complexMonicDepressedP a b = 0) (hu : u ^ 3 = -complexMonicDepressedQ a b c) :
    (monicCubic a b c).roots =
      {u - a / 3, u * omega - a / 3, u * omega ^ 2 - a / 3} := by
  refine monicCubic_roots_of_forall_eq fun x => ?_
  unfold complexMonicDepressedP at hp
  unfold complexMonicDepressedQ at hu
  linear_combination (x + a / 3) * hp + hu +
    (u * (x + a / 3) ^ 2 - u ^ 2 * (x + a / 3) * omega) * omega_quadratic +
    u ^ 3 * omega_cube

/-- When the first radicand `A` is nonzero and `u` is a cube root of it, `u`
and the quotient `-p / (3 * u)` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_of_cube_eq_radicandPlus {a b c u : ℂ}
    (hu : u ^ 3 =
      radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c))
    (hA : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {u + -complexMonicDepressedP a b / (3 * u) - a / 3,
        omega * u + omega ^ 2 * (-complexMonicDepressedP a b / (3 * u)) - a / 3,
        omega ^ 2 * u + omega * (-complexMonicDepressedP a b / (3 * u)) - a / 3} := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hA (by rw [← hu]; ring)
  have hv : (-complexMonicDepressedP a b / (3 * u)) ^ 3 =
      radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) := by
    rw [div_pow, mul_pow, hu, div_eq_iff (mul_ne_zero (by norm_num) hA)]
    linear_combination (-27 : ℂ) *
      radicands_product (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
  exact monicCubic_roots_of_compatible_pair (by rw [hu, hv, radicands_sum]) (by field_simp)

/-- When the first radicand is nonzero, the principal cube root of it and the
quotient `-p / (3 * u)` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_principalQuotient {a b c : ℂ}
    (hA : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {(principalQuotientMonicCubicRoots a b c).x₀,
        (principalQuotientMonicCubicRoots a b c).x₁,
        (principalQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_of_cube_eq_radicandPlus (principal_cube _) hA

/-- When the first radicand is nonzero, the modified principal cube root of it
and the quotient `-p / (3 * u)` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_quotient {a b c : ℂ}
    (hA : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {(quotientMonicCubicRoots a b c).x₀,
        (quotientMonicCubicRoots a b c).x₁,
        (quotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_of_cube_eq_radicandPlus (modifiedPrincipal_cube _) hA

/-- When the second radicand `B` is nonzero and `v` is a cube root of it, the
quotient `-p / (3 * v)` and `v` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_of_cube_eq_radicandMinus {a b c v : ℂ}
    (hv : v ^ 3 =
      radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c))
    (hB : radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {-complexMonicDepressedP a b / (3 * v) + v - a / 3,
        omega * (-complexMonicDepressedP a b / (3 * v)) + omega ^ 2 * v - a / 3,
        omega ^ 2 * (-complexMonicDepressedP a b / (3 * v)) + omega * v - a / 3} := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hB (by rw [← hv]; ring)
  have hu : (-complexMonicDepressedP a b / (3 * v)) ^ 3 =
      radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) := by
    rw [div_pow, mul_pow, hv, div_eq_iff (mul_ne_zero (by norm_num) hB)]
    linear_combination (-27 : ℂ) *
      radicands_product (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
  exact monicCubic_roots_of_compatible_pair (by rw [hu, hv, radicands_sum]) (by field_simp)

/-- When the second radicand is nonzero, the formula built on it gives the
roots of the cubic with multiplicity. -/
theorem monicCubic_roots_secondRadicandQuotient {a b c : ℂ}
    (hB : radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {(secondRadicandQuotientMonicCubicRoots a b c).x₀,
        (secondRadicandQuotientMonicCubicRoots a b c).x₁,
        (secondRadicandQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_of_cube_eq_radicandMinus
    (v := -principal
      (-radicandMinus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)))
    (by rw [neg_pow, principal_cube]; ring) hB

end CubicEquation.CardanoComplex
