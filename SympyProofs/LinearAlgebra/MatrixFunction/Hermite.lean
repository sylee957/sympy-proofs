module

public import SympyProofs.LinearAlgebra.MatrixFunction.Primary
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Exact Hermite representations of matrix functions

The local Taylor polynomials are joined by the Chinese remainder theorem.
Reducing the result modulo the minimal polynomial of the matrix preserves its
value and gives a representative of degree strictly below that minimal polynomial.
No Jordan basis is chosen. The interpolant selection is noncomputable; the
polynomial identities also apply to explicitly supplied interpolation data.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermite interpolant reduced modulo the minimal polynomial of `A`. -/
noncomputable def matrixHermitePolynomial (A : Matrix n n ℂ) (q : ℂ → ℂ[X]) : ℂ[X] :=
  primaryPolynomial (Matrix.toLinAlgEquiv' A) q %ₘ minpoly ℂ A

theorem matrixHermitePolynomial_degree_lt (A : Matrix n n ℂ) (q : ℂ → ℂ[X]) :
    (matrixHermitePolynomial A q).degree < (minpoly ℂ A).degree :=
  degree_modByMonic_lt _ (minpoly.monic (Algebra.IsIntegral.isIntegral A))

theorem aeval_matrixHermitePolynomial (A : Matrix n n ℂ) (q : ℂ → ℂ[X]) :
    aeval A (matrixHermitePolynomial A q) =
      aeval A (primaryPolynomial (Matrix.toLinAlgEquiv' A) q) :=
  minpoly.aeval_modByMonic_minpoly _ _

theorem toLin_aeval_matrixHermitePolynomial (A : Matrix n n ℂ) (q : ℂ → ℂ[X]) :
    Matrix.toLinAlgEquiv' (aeval A (matrixHermitePolynomial A q)) =
      primaryFunction (Matrix.toLinAlgEquiv' A) q := by
  rw [aeval_matrixHermitePolynomial, ← aeval_algHom_apply, primaryFunction]

/-- Any supplied polynomial with the required Hermite residues evaluates to
the same matrix, regardless of which interpolant the existence proof chooses. -/
theorem aeval_matrixHermitePolynomial_eq (A : Matrix n n ℂ) (q : ℂ → ℂ[X]) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ A, (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣ p - q a) :
    aeval A (matrixHermitePolynomial A q) = aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [toLin_aeval_matrixHermitePolynomial, ← aeval_algHom_apply]
  apply primaryFunction_eq_aeval
  simpa only [AlgEquiv.spectrum_eq] using hp

/-- Polynomial congruence modulo the minimal polynomial is an exact evaluation certificate. -/
theorem aeval_eq_of_minpoly_dvd_sub (A : Matrix n n ℂ) {p q : ℂ[X]}
    (h : minpoly ℂ A ∣ p - q) : aeval A p = aeval A q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact minpoly.dvd_iff.mp h

/-- Below the minimal-polynomial degree, evaluation has a unique representative. -/
theorem matrix_polynomial_unique (A : Matrix n n ℂ) {p q : ℂ[X]}
    (hp : p.degree < (minpoly ℂ A).degree) (hq : q.degree < (minpoly ℂ A).degree)
    (heq : aeval A p = aeval A q) : p = q := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt
  · apply minpoly.dvd ℂ A
    rw [map_sub, heq, sub_self]
  · exact (degree_sub_le p q).trans_lt (max_lt hp hq)

end SympyProofs.MatrixExponential
