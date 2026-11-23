module

public import SympyProofs.CubicEquation.CardanoComplex.CompatiblePair
public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Realness

/-!
# The roots of a monic cubic, with multiplicity: the rules of a cubic solver

`monicCubic a b c` is the polynomial `X^3 + a*X^2 + b*X + c` over the complex
numbers, defined in `MonicPolynomial.lean`. Its `roots` is a multiset, so it
records each root with its multiplicity.

Each theorem here is one rule of a cubic solver: a condition on the
coefficients that can be tested, and the multiset of roots under it. Write
`p = b - a^2/3` and `q = 2*a^3/27 - a*b/3 + c` for the depressed coefficients,
`Δ = q^2/4 + p^3/27`, and `A = -q/2 + sqrt Δ`, `B = -q/2 - sqrt Δ` for the two
radicands. The general statements that the rules are proved from are in
`CompatiblePair.lean`.

Special coefficients:

* `c = 0`: `0` and the roots of `X^2 + a*X + b`
  (`monicCubic_roots_of_constant_eq_zero`).
* `p = 0` and `q = 0`: `-a/3` three times (`monicCubic_roots_of_depressed_eq_zero`).
* `p = 0`: the cube roots of `-q`, shifted, from the principal cube root of `-q`
  (`monicCubic_roots_of_depressedP_eq_zero_principal`) or from minus the
  principal cube root of `q` (`monicCubic_roots_of_depressedP_eq_zero_neg_principal`).
* `q = 0`: `0` and the roots of `Y^2 + p`, shifted
  (`monicCubic_roots_of_depressedQ_eq_zero_of_quadratic_roots`).
* `Δ = 0` and `p ≠ 0`: a simple and a double root without radicals
  (`monicCubic_roots_of_discriminant_eq_zero`).

Cardano's formula, by the position of `q`:

* `q` with negative real part (`monicCubic_roots_of_depressedQ_re_neg`) or on
  the negative imaginary axis
  (`monicCubic_roots_of_depressedQ_re_eq_zero_of_im_neg`): the principal cube
  root `u` of `A` and `v = -p / (3 * u)`;
* `q` with positive real part (`monicCubic_roots_of_depressedQ_re_pos`) or on
  the positive imaginary axis
  (`monicCubic_roots_of_depressedQ_re_eq_zero_of_im_pos`): `v = -(-B)^(1/3)`
  and `u = -p / (3 * v)`;
* `p ≠ 0`: the modified principal cube root `u` of `A` and `v = -p / (3 * u)`
  (`monicCubic_roots_quotient_of_depressedP_ne_zero`);
* no condition: the modulus-and-phase formula (`monicCubic_roots_modulusPhase`).

Real coefficients:

* no further condition: the modified-principal formula
  (`monicCubic_roots_modifiedPrincipal`);
* `0 ≤ Δ`: two real cube roots (`monicCubic_roots_of_discriminant_nonneg`);
* `Δ < 0`: the real and imaginary parts of one principal cube root
  (`monicCubic_roots_of_discriminant_neg`);
* `q < 0`: the principal cube root of `A` and the quotient
  (`monicCubic_roots_of_depressedQ_neg`);
* `0 < q`: the formula built on `B` (`monicCubic_roots_of_depressedQ_pos`).
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open CardanoReal
open Complex

/-! ### Zero constant coefficient -/

/-- If `x₁` and `x₂` are the roots of `X^2 + a*X + b`, the roots of
`X^3 + a*X^2 + b*X` are `0`, `x₁` and `x₂`. -/
theorem monicCubic_roots_of_constant_eq_zero {a b x₁ x₂ : ℂ}
    (h : (monicQuadratic a b).roots = {x₁, x₂}) :
    (monicCubic a b 0).roots = {0, x₁, x₂} := by
  obtain ⟨hsum, hprod⟩ := monicQuadratic_roots_eq_pair_iff.mp h
  refine monicCubic_roots_of_forall_eq fun x => ?_
  linear_combination x ^ 2 * hsum - x * hprod

/-- The roots of `X^3 + a*X^2 + b*X` are `0` and the two values of the
quadratic formula for `X^2 + a*X + b`. -/
theorem monicCubic_roots_constant_zero (a b : ℂ) :
    (monicCubic a b 0).roots =
      {0, (-a - Complex.sqrt (a ^ 2 - 4 * b)) / 2,
        (-a + Complex.sqrt (a ^ 2 - 4 * b)) / 2} :=
  monicCubic_roots_of_constant_eq_zero (monicQuadratic_roots a b)

/-! ### Zero depressed linear coefficient -/

/-- When `p = 0` and `q = 0`, the roots of the cubic with multiplicity are
`-a/3` three times. -/
theorem monicCubic_roots_of_depressed_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b = 0) (hq : complexMonicDepressedQ a b c = 0) :
    (monicCubic a b c).roots = {-(a / 3), -(a / 3), -(a / 3)} := by
  refine monicCubic_roots_of_forall_eq fun x => ?_
  unfold complexMonicDepressedP at hp
  unfold complexMonicDepressedQ at hq
  linear_combination (x + a / 3) * hp + hq

/-- When `p = 0`, the roots are given by the principal cube root of `-q`. -/
theorem monicCubic_roots_of_depressedP_eq_zero_principal {a b c : ℂ}
    (hp : complexMonicDepressedP a b = 0) :
    (monicCubic a b c).roots =
      {principal (-complexMonicDepressedQ a b c) - a / 3,
        principal (-complexMonicDepressedQ a b c) * omega - a / 3,
        principal (-complexMonicDepressedQ a b c) * omega ^ 2 - a / 3} :=
  monicCubic_roots_of_depressedP_eq_zero hp (principal_cube _)

/-- When `p = 0`, the roots are given by minus the principal cube root of `q`. -/
theorem monicCubic_roots_of_depressedP_eq_zero_neg_principal {a b c : ℂ}
    (hp : complexMonicDepressedP a b = 0) :
    (monicCubic a b c).roots =
      {-principal (complexMonicDepressedQ a b c) - a / 3,
        -principal (complexMonicDepressedQ a b c) * omega - a / 3,
        -principal (complexMonicDepressedQ a b c) * omega ^ 2 - a / 3} :=
  monicCubic_roots_of_depressedP_eq_zero hp
    (by rw [neg_pow, principal_cube]; norm_num)

/-! ### Zero depressed constant coefficient -/

/-- If `q = 0` and `y₁`, `y₂` are the roots of `Y^2 + p`, the roots of
`X^3 + a*X^2 + b*X + c` are `-a/3`, `y₁ - a/3` and `y₂ - a/3`. -/
theorem monicCubic_roots_of_depressedQ_eq_zero_of_quadratic_roots {a b c y₁ y₂ : ℂ}
    (hq : complexMonicDepressedQ a b c = 0)
    (h : (monicQuadratic 0 (complexMonicDepressedP a b)).roots = {y₁, y₂}) :
    (monicCubic a b c).roots = {-(a / 3), y₁ - a / 3, y₂ - a / 3} := by
  obtain ⟨hsum, hprod⟩ := monicQuadratic_roots_eq_pair_iff.mp h
  refine monicCubic_roots_of_forall_eq fun x => ?_
  unfold complexMonicDepressedQ at hq
  unfold complexMonicDepressedP at hprod
  linear_combination hq + (x + a / 3) ^ 2 * hsum - (x + a / 3) * hprod

/-- If `q = 0`, the roots of `X^3 + a*X^2 + b*X + c` are `-a/3` and the two
square roots of `-p`, shifted by `-a/3`. -/
theorem monicCubic_roots_of_depressedQ_eq_zero {a b c : ℂ}
    (hq : complexMonicDepressedQ a b c = 0) :
    (monicCubic a b c).roots =
      {-(a / 3), -Complex.sqrt (-complexMonicDepressedP a b) - a / 3,
        Complex.sqrt (-complexMonicDepressedP a b) - a / 3} :=
  monicCubic_roots_of_depressedQ_eq_zero_of_quadratic_roots hq (monicQuadratic_roots_pure _)

/-! ### Zero discriminant -/

/-- When `Δ = 0` and `p ≠ 0`, the roots of the cubic with multiplicity are
`3*q/p - a/3` once and `-3*q/(2*p) - a/3` twice. -/
theorem monicCubic_roots_of_discriminant_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b ≠ 0)
    (hD : discriminant (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0) :
    (monicCubic a b c).roots =
      {3 * complexMonicDepressedQ a b c / complexMonicDepressedP a b - a / 3,
        -(3 * complexMonicDepressedQ a b c / (2 * complexMonicDepressedP a b)) - a / 3,
        -(3 * complexMonicDepressedQ a b c / (2 * complexMonicDepressedP a b)) - a / 3} := by
  refine monicCubic_roots_of_forall_eq fun x => ?_
  have hx : x ^ 3 + a * x ^ 2 + b * x + c =
      (x + a / 3) ^ 3 + complexMonicDepressedP a b * (x + a / 3) +
        complexMonicDepressedQ a b c := by
    unfold complexMonicDepressedP complexMonicDepressedQ
    ring
  rw [hx]
  unfold discriminant at hD
  generalize complexMonicDepressedP a b = P at hp hD ⊢
  generalize complexMonicDepressedQ a b c = Q at hD ⊢
  have hr : P * (3 * Q / P) = 3 * Q := mul_div_cancel₀ _ hp
  have hhalf : 3 * Q / (2 * P) = 3 * Q / P / 2 := by ring
  rw [hhalf]
  generalize 3 * Q / P = r at hr ⊢
  have hsq : 3 * r ^ 2 + 4 * P = 0 := by
    have h : P ^ 2 * (3 * r ^ 2 + 4 * P) = 0 := by
      linear_combination 3 * (P * r + 3 * Q) * hr + 108 * hD
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hp)
  linear_combination ((x + a / 3) / 4 + r / 12) * hsq - (1 / 3 : ℂ) * hr

/-! ### Cardano's formula -/

/-- When `q` has negative real part, the principal cube root of the first
radicand and the quotient `-p / (3 * u)` give the roots of the cubic. -/
theorem monicCubic_roots_of_depressedQ_re_neg {a b c : ℂ}
    (h : (complexMonicDepressedQ a b c).re < 0) :
    (monicCubic a b c).roots =
      {(principalQuotientMonicCubicRoots a b c).x₀,
        (principalQuotientMonicCubicRoots a b c).x₁,
        (principalQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_principalQuotient
    (slitPlane_ne_zero (radicandPlus_mem_slitPlane_of_re_neg _ h))

/-- When `q` lies on the negative imaginary axis, the principal cube root of
the first radicand and the quotient `-p / (3 * u)` give the roots of the
cubic. -/
theorem monicCubic_roots_of_depressedQ_re_eq_zero_of_im_neg {a b c : ℂ}
    (hre : (complexMonicDepressedQ a b c).re = 0)
    (him : (complexMonicDepressedQ a b c).im < 0) :
    (monicCubic a b c).roots =
      {(principalQuotientMonicCubicRoots a b c).x₀,
        (principalQuotientMonicCubicRoots a b c).x₁,
        (principalQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_principalQuotient
    (radicandPlus_ne_zero_of_re_eq_zero_of_im_neg _ hre him)

/-- When `q` has positive real part, the formula built on the second radicand
gives the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_of_depressedQ_re_pos {a b c : ℂ}
    (h : 0 < (complexMonicDepressedQ a b c).re) :
    (monicCubic a b c).roots =
      {(secondRadicandQuotientMonicCubicRoots a b c).x₀,
        (secondRadicandQuotientMonicCubicRoots a b c).x₁,
        (secondRadicandQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_secondRadicandQuotient (radicandMinus_ne_zero_of_re_pos _ h)

/-- When `q` lies on the positive imaginary axis, the formula built on the
second radicand gives the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_of_depressedQ_re_eq_zero_of_im_pos {a b c : ℂ}
    (hre : (complexMonicDepressedQ a b c).re = 0)
    (him : 0 < (complexMonicDepressedQ a b c).im) :
    (monicCubic a b c).roots =
      {(secondRadicandQuotientMonicCubicRoots a b c).x₀,
        (secondRadicandQuotientMonicCubicRoots a b c).x₁,
        (secondRadicandQuotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_secondRadicandQuotient
    (radicandMinus_ne_zero_of_re_eq_zero_of_im_pos _ hre him)

/-- When `p ≠ 0`, the modified principal cube root of the first radicand and
the quotient `-p / (3 * u)` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_quotient_of_depressedP_ne_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b ≠ 0) :
    (monicCubic a b c).roots =
      {(quotientMonicCubicRoots a b c).x₀,
        (quotientMonicCubicRoots a b c).x₁,
        (quotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_quotient (radicandPlus_ne_zero_of_ne_zero hp _)

/-- The modulus-and-phase formula gives the roots of the cubic with
multiplicity, for arbitrary complex coefficients. -/
theorem monicCubic_roots_modulusPhase (a b c : ℂ) :
    (monicCubic a b c).roots =
      {(modulusPhaseMonicCubicRoots a b c).x₀,
        (modulusPhaseMonicCubicRoots a b c).x₁,
        (modulusPhaseMonicCubicRoots a b c).x₂} := by
  have hpair := modulusPhase_pair (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)
  rw [modulusPhaseMonicCubicRoots_x₀_eq, modulusPhaseMonicCubicRoots_x₁_eq,
    modulusPhaseMonicCubicRoots_x₂_eq]
  refine monicCubic_roots_of_compatible_pair ?_ hpair.2
  rw [modifiedConjugateCorrectedU, modifiedPrincipal_cube, hpair.1, radicands_sum]

/-! ### Real coefficients -/

/-- For real coefficients, the modified-principal formula gives the roots of
the cubic with multiplicity. -/
theorem monicCubic_roots_modifiedPrincipal (a b c : ℝ) :
    (monicCubic (a : ℂ) b c).roots =
      {(modifiedPrincipalMonicCubicRoots a b c).x₀,
        (modifiedPrincipalMonicCubicRoots a b c).x₁,
        (modifiedPrincipalMonicCubicRoots a b c).x₂} := by
  have hshift : ((a / 3 : ℝ) : ℂ) = (a : ℂ) / 3 := by push_cast; ring
  rw [modifiedPrincipalMonicCubicRoots_x₀_eq, modifiedPrincipalMonicCubicRoots_x₁_eq,
    modifiedPrincipalMonicCubicRoots_x₂_eq, hshift]
  refine monicCubic_roots_of_compatible_pair ?_ ?_
  · rw [complexMonicDepressedQ_ofReal, modifiedU, modifiedV, modifiedPrincipal_cube,
      modifiedPrincipal_cube, radicands_sum]
  · rw [complexMonicDepressedP_ofReal, modifiedU_mul_modifiedV]

/-- For real coefficients and nonnegative discriminant, the roots of the cubic
with multiplicity are given by real cube roots. -/
theorem monicCubic_roots_of_discriminant_nonneg {a b c : ℝ}
    (h : 0 ≤ monicCubicDiscriminant a b c) :
    (monicCubic (a : ℂ) b c).roots =
      {(realRadicalMonicCubicRoots a b c).x₀,
        (realRadicalMonicCubicRoots a b c).x₁,
        (realRadicalMonicCubicRoots a b c).x₂} := by
  rw [← modifiedPrincipalMonicCubicRoots_eq_realRadical h]
  exact monicCubic_roots_modifiedPrincipal a b c

/-- For real coefficients and negative discriminant, the roots of the cubic
with multiplicity are given by the real and imaginary parts of one principal
cube root. -/
theorem monicCubic_roots_of_discriminant_neg {a b c : ℝ}
    (h : monicCubicDiscriminant a b c < 0) :
    (monicCubic (a : ℂ) b c).roots =
      {(singleRadicalMonicCubicRoots a b c).x₀,
        (singleRadicalMonicCubicRoots a b c).x₁,
        (singleRadicalMonicCubicRoots a b c).x₂} := by
  rw [← modifiedPrincipalMonicCubicRoots_eq_singleRadical h]
  exact monicCubic_roots_modifiedPrincipal a b c

/-- For real coefficients with `q < 0`, the principal cube root of the first
radicand and the quotient `-p / (3 * u)` give the roots of the cubic. This is
the case of negative real part, since a real `q` is its own real part. -/
theorem monicCubic_roots_of_depressedQ_neg {a b c : ℝ} (h : monicDepressedQ a b c < 0) :
    (monicCubic (a : ℂ) b c).roots =
      {(principalQuotientMonicCubicRoots (a : ℂ) b c).x₀,
        (principalQuotientMonicCubicRoots (a : ℂ) b c).x₁,
        (principalQuotientMonicCubicRoots (a : ℂ) b c).x₂} :=
  monicCubic_roots_of_depressedQ_re_neg
    (by rw [complexMonicDepressedQ_ofReal, ofReal_re]; exact h)

/-- For real coefficients with `0 < q`, the formula built on the second
radicand gives the roots of the cubic with multiplicity. This is the case of
positive real part, since a real `q` is its own real part. -/
theorem monicCubic_roots_of_depressedQ_pos {a b c : ℝ} (h : 0 < monicDepressedQ a b c) :
    (monicCubic (a : ℂ) b c).roots =
      {(secondRadicandQuotientMonicCubicRoots (a : ℂ) b c).x₀,
        (secondRadicandQuotientMonicCubicRoots (a : ℂ) b c).x₁,
        (secondRadicandQuotientMonicCubicRoots (a : ℂ) b c).x₂} :=
  monicCubic_roots_of_depressedQ_re_pos
    (by rw [complexMonicDepressedQ_ofReal, ofReal_re]; exact h)

end CubicEquation.CardanoComplex
