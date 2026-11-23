module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Shortcuts
public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Realness

/-!
# The roots of a monic cubic, with multiplicity

`monicCubic a b c` is the polynomial `X^3 + a*X^2 + b*X + c` over the complex
numbers. Its `roots` is a multiset, so it records each root with its
multiplicity. This file gives that multiset in every case that a cubic solver
distinguishes. Write `p = b - a^2/3` and `q = 2*a^3/27 - a*b/3 + c` for the
depressed coefficients, `Δ = q^2/4 + p^3/27`, and `A = -q/2 + sqrt Δ` for the
first radicand.

Special coefficients:

* `c = 0`: `0` and the roots of `X^2 + a*X + b`
  (`monicCubic_roots_of_constant_eq_zero`).
* `p = 0` and `q = 0`: `-a/3` three times (`monicCubic_roots_of_depressed_eq_zero`).
* `p = 0`: the cube roots of `-q`, shifted (`monicCubic_roots_of_depressedP_eq_zero`).
* `q = 0`: `0` and the roots of `Y^2 + p`, shifted
  (`monicCubic_roots_of_depressedQ_eq_zero_of_quadratic_roots`).
* `Δ = 0` and `p ≠ 0`: a simple and a double root without radicals
  (`monicCubic_roots_of_discriminant_eq_zero`).

Cardano's formula. Every form comes from `monicCubic_roots_of_compatible_pair`,
which takes any `U`, `V` with `U^3 + V^3 = -q` and `U * V = -p/3`:

* any cube root `u` of `A ≠ 0` with `v = -p / (3 * u)`
  (`monicCubic_roots_of_cube_eq_radicandPlus`), in particular the principal
  cube root (`monicCubic_roots_principalQuotient`) and the modified principal
  cube root (`monicCubic_roots_quotient`);
* the modulus-and-phase formula, with no condition on the coefficients
  (`monicCubic_roots_modulusPhase`).

Real coefficients:

* the modified-principal formula, with no further condition
  (`monicCubic_roots_modifiedPrincipal`);
* `0 ≤ Δ`: two real cube roots (`monicCubic_roots_of_discriminant_nonneg`);
* `Δ < 0`: the real and imaginary parts of one principal cube root
  (`monicCubic_roots_of_discriminant_neg`);
* `q < 0`: the principal cube root and the quotient
  (`monicCubic_roots_of_depressedQ_neg`).
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open CardanoReal
open Complex

/-! ### The polynomials -/

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

/-- When `p = 0` and `q = 0` the cubic is the cube of `x + a/3`. -/
theorem monic_cubic_eq_cube {a b c : ℂ} (hp : complexMonicDepressedP a b = 0)
    (hq : complexMonicDepressedQ a b c = 0) (x : ℂ) :
    x ^ 3 + a * x ^ 2 + b * x + c = (x + a / 3) ^ 3 := by
  unfold complexMonicDepressedP at hp
  unfold complexMonicDepressedQ at hq
  linear_combination (x + a / 3) * hp + hq

/-- When `p = 0` and `q = 0`, the roots of the cubic with multiplicity are
`-a/3` three times. -/
theorem monicCubic_roots_of_depressed_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b = 0) (hq : complexMonicDepressedQ a b c = 0) :
    (monicCubic a b c).roots = {-(a / 3), -(a / 3), -(a / 3)} :=
  monicCubic_roots_of_forall_eq fun x => by
    rw [monic_cubic_eq_cube hp hq x]
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

/-- For a nonnegative real `q`, minus the principal cube root of `q` is the
real number `-q^(1/3)`. -/
theorem neg_principal_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    -principal (r : ℂ) = ((-(r ^ (3⁻¹ : ℝ)) : ℝ) : ℂ) := by
  rw [principal_ofReal_of_nonneg hr, ofReal_neg]

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

/-- When `Δ = 0` and `p ≠ 0`, the cubic is `x - (3*q/p - a/3)` times the square
of `x - (-3*q/(2*p) - a/3)`. -/
theorem monic_cubic_eq_of_discriminant_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b ≠ 0)
    (hD : discriminant (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0)
    (x : ℂ) :
    x ^ 3 + a * x ^ 2 + b * x + c =
      (x - (3 * complexMonicDepressedQ a b c / complexMonicDepressedP a b - a / 3)) *
        (x - (-(3 * complexMonicDepressedQ a b c / (2 * complexMonicDepressedP a b)) -
          a / 3)) ^ 2 := by
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

/-- When `Δ = 0` and `p ≠ 0`, the roots of the cubic with multiplicity are
`3*q/p - a/3` once and `-3*q/(2*p) - a/3` twice. -/
theorem monicCubic_roots_of_discriminant_eq_zero {a b c : ℂ}
    (hp : complexMonicDepressedP a b ≠ 0)
    (hD : discriminant (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) = 0) :
    (monicCubic a b c).roots =
      {3 * complexMonicDepressedQ a b c / complexMonicDepressedP a b - a / 3,
        -(3 * complexMonicDepressedQ a b c / (2 * complexMonicDepressedP a b)) - a / 3,
        -(3 * complexMonicDepressedQ a b c / (2 * complexMonicDepressedP a b)) - a / 3} :=
  monicCubic_roots_of_forall_eq fun x => by
    rw [monic_cubic_eq_of_discriminant_eq_zero hp hD x]
    ring

/-! ### Cardano's formula -/

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

/-- When `q` has negative real part, or the first radicand `A` has nonzero
imaginary part, or `A` has positive real part, the principal cube root of `A`
and the quotient `-p / (3 * u)` give the roots of the cubic. -/
theorem monicCubic_roots_principalQuotient_of_or {a b c : ℂ}
    (h : (complexMonicDepressedQ a b c).re < 0 ∨
      (radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)).im ≠ 0 ∨
      0 < (radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c)).re) :
    (monicCubic a b c).roots =
      {(principalQuotientMonicCubicRoots a b c).x₀,
        (principalQuotientMonicCubicRoots a b c).x₁,
        (principalQuotientMonicCubicRoots a b c).x₂} := by
  rcases h with h | h | h
  · exact monicCubic_roots_of_depressedQ_re_neg h
  · exact monicCubic_roots_principalQuotient fun h0 => h (by rw [h0, zero_im])
  · exact monicCubic_roots_principalQuotient fun h0 => h.ne' (by rw [h0, zero_re])

/-- When the first radicand is nonzero, the modified principal cube root of it
and the quotient `-p / (3 * u)` give the roots of the cubic with multiplicity. -/
theorem monicCubic_roots_quotient {a b c : ℂ}
    (hA : radicandPlus (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) ≠ 0) :
    (monicCubic a b c).roots =
      {(quotientMonicCubicRoots a b c).x₀,
        (quotientMonicCubicRoots a b c).x₁,
        (quotientMonicCubicRoots a b c).x₂} :=
  monicCubic_roots_of_cube_eq_radicandPlus (modifiedPrincipal_cube _) hA

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
radicand and the quotient `-p / (3 * u)` give the roots of the cubic. -/
theorem monicCubic_roots_of_depressedQ_neg {a b c : ℝ} (h : monicDepressedQ a b c < 0) :
    (monicCubic (a : ℂ) b c).roots =
      {(principalQuotientMonicCubicRoots (a : ℂ) b c).x₀,
        (principalQuotientMonicCubicRoots (a : ℂ) b c).x₁,
        (principalQuotientMonicCubicRoots (a : ℂ) b c).x₂} :=
  monicCubic_roots_of_depressedQ_re_neg
    (by rw [complexMonicDepressedQ_ofReal, ofReal_re]; exact h)

end CubicEquation.CardanoComplex
