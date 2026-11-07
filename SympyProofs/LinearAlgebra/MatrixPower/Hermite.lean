module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Hermite
public import SympyProofs.LinearAlgebra.MatrixExponential.Hermite
public import SympyProofs.LinearAlgebra.MatrixPower.MatrixExponent

/-!
# Exact algebraic matrix--matrix powers by Hermite interpolation

Choose a logarithm interpolant `p` for `A`, put `C = p(A) * B`, and choose an
exponential interpolant `q` for `C`. Then `A^B = q(C)`. Both polynomials are
reduced modulo the minimal polynomial of the matrix where they are evaluated.
No Jordan basis, matrix logarithm, or matrix exponential occurs in the defining
expression: all matrix operations are finite polynomial evaluation and multiplication.
The coefficients may contain scalar logarithms and exponentials, so "exact"
does not mean "algebraic-number valued".

The polynomial choices are noncomputable specifications, not a benchmarked
symbolic algorithm. `matrixPowFromPolynomials` and its verification theorem
also support externally supplied exact polynomial data.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reduced Hermite polynomial for a scalar exponent, including singular bases. -/
noncomputable def cpowHermitePolynomial (A : Matrix n n ℂ) (z : ℂ) : ℂ[X] :=
  matrixHermitePolynomial A
    (fun a => localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1))

theorem cpowHermitePolynomial_degree_lt (A : Matrix n n ℂ) (z : ℂ) :
    (cpowHermitePolynomial A z).degree < (minpoly ℂ A).degree :=
  matrixHermitePolynomial_degree_lt A _

theorem aeval_cpowHermitePolynomial (A : Matrix n n ℂ) (z : ℂ) :
    aeval A (cpowHermitePolynomial A z) = matrixCpow A z := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [cpowHermitePolynomial, toLin_aeval_matrixHermitePolynomial, toLin_matrixCpow, endCpow]

/-- Finite algebraic evaluation with explicitly supplied logarithm/exponential polynomials. -/
noncomputable def matrixPowFromPolynomials (A B : Matrix n n ℂ) (p q : ℂ[X]) :
    Matrix n n ℂ := aeval (aeval A p * B) q

/-- The exact Hermite construction. Correctness as a matrix power requires `IsUnit A`. -/
noncomputable def hermiteMatrixPow (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixPowFromPolynomials A B (logHermitePolynomial A)
    (expHermitePolynomial (aeval A (logHermitePolynomial A) * B))

theorem hermiteMatrixPow_eq_halfOpenMatrixPow (A B : Matrix n n ℂ) (hA : IsUnit A) :
    hermiteMatrixPow A B = halfOpenMatrixPow A B := by
  rw [hermiteMatrixPow, matrixPowFromPolynomials, aeval_expHermitePolynomial,
    aeval_logHermitePolynomial A hA, halfOpenMatrixPow]

theorem hermiteMatrixPow_eq_principalMatrixPow (A B : Matrix n n ℂ)
    (hA : HasSlitSpectrum A) : hermiteMatrixPow A B = principalMatrixPow A B := by
  rw [hermiteMatrixPow_eq_halfOpenMatrixPow A B hA.isUnit,
    halfOpenMatrixPow_eq_principalMatrixPow A B hA]

theorem hermiteMatrixPow_scalar (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    hermiteMatrixPow A (z • 1) = matrixCpow A z := by
  rw [hermiteMatrixPow_eq_halfOpenMatrixPow A _ hA,
    halfOpenMatrixPow_scalar_eq_matrixCpow A hA]

/-- Check exact polynomial data using the local Taylor congruences. The
exponential conditions concern `p(A) * B`, even if `A` and `B` do not commute. -/
theorem matrixPowFromPolynomials_eq_halfOpenMatrixPow (A B : Matrix n n ℂ)
    (hA : IsUnit A) (p q : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ A, (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
      p - localLogPolynomial a (Module.finrank ℂ (n → ℂ) + 1))
    (hq : ∀ a ∈ spectrum ℂ (aeval A p * B),
      (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
        q - localExpPolynomial a (Module.finrank ℂ (n → ℂ) + 1)) :
    matrixPowFromPolynomials A B p q = halfOpenMatrixPow A B := by
  rw [matrixPowFromPolynomials, ← exp_eq_aeval_of_interpolation _ q hq,
    ← halfOpenLog_eq_aeval_of_interpolation A hA p hp, halfOpenMatrixPow]

/-- Reduced polynomials can instead be certified by congruences modulo the
two minimal polynomials, without imposing the oversized Taylor conditions. -/
theorem matrixPowFromPolynomials_eq_of_minpoly_congruence (A B : Matrix n n ℂ)
    (hA : IsUnit A) (p q : ℂ[X])
    (hp : minpoly ℂ A ∣ p - logHermitePolynomial A)
    (hq : minpoly ℂ (aeval A p * B) ∣ q - expHermitePolynomial (aeval A p * B)) :
    matrixPowFromPolynomials A B p q = halfOpenMatrixPow A B := by
  rw [matrixPowFromPolynomials, aeval_eq_of_minpoly_dvd_sub _ hq,
    aeval_expHermitePolynomial, aeval_eq_of_minpoly_dvd_sub _ hp,
    aeval_logHermitePolynomial A hA, halfOpenMatrixPow]

/-- The matrix power has an exact two-polynomial representation with degrees
bounded by the two minimal polynomials, including noncommuting exponents. -/
theorem exists_reduced_polynomials_matrixPow (A B : Matrix n n ℂ) (hA : IsUnit A) :
    ∃ p q : ℂ[X], p.degree < (minpoly ℂ A).degree ∧
      q.degree < (minpoly ℂ (aeval A p * B)).degree ∧
      halfOpenMatrixPow A B = matrixPowFromPolynomials A B p q := by
  refine ⟨logHermitePolynomial A,
    expHermitePolynomial (aeval A (logHermitePolynomial A) * B),
    logHermitePolynomial_degree_lt A, expHermitePolynomial_degree_lt _, ?_⟩
  exact (hermiteMatrixPow_eq_halfOpenMatrixPow A B hA).symm

end SympyProofs.MatrixExponential
