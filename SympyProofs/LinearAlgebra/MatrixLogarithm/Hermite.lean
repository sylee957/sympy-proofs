module

public import SympyProofs.LinearAlgebra.MatrixFunction.Hermite
public import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenLogarithm

/-!
# Exact Hermite polynomials for matrix logarithms

`logHermitePolynomial A` is a finite polynomial, reduced modulo `minpoly ℂ A`,
whose evaluation equals the half-open logarithm when `A` is invertible. Local
Taylor congruences express Hermite interpolation without constructing a Jordan
basis. Explicitly supplied interpolants are accepted by the verification rule.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A reduced exact logarithm polynomial; its logarithm specification requires
invertibility, but the polynomial itself takes only the matrix as input. -/
noncomputable def logHermitePolynomial (A : Matrix n n ℂ) : ℂ[X] :=
  matrixHermitePolynomial A (fun a => localLogPolynomial a (Module.finrank ℂ (n → ℂ) + 1))

theorem logHermitePolynomial_degree_lt (A : Matrix n n ℂ) :
    (logHermitePolynomial A).degree < (minpoly ℂ A).degree :=
  matrixHermitePolynomial_degree_lt A _

theorem aeval_logHermitePolynomial (A : Matrix n n ℂ) (hA : IsUnit A) :
    aeval A (logHermitePolynomial A) = halfOpenLog A := by
  rw [logHermitePolynomial, aeval_matrixHermitePolynomial]
  let f := Matrix.toLinAlgEquiv' A
  let d := Module.finrank ℂ (n → ℂ) + 1
  let p := primaryPolynomial f (fun a => localLogPolynomial a d)
  have hp : ∀ a ∈ spectrum ℂ f, (X - C a) ^ d ∣ p - localLogPolynomial a d :=
    primaryPolynomial_spec f _
  change aeval A p = halfOpenLog A
  apply halfOpenLog_unique A _ hA
  constructor
  · apply Matrix.toLinAlgEquiv'.injective
    rw [toLin_exp, ← aeval_algHom_apply]
    apply endExp_logInterpolation_of_nonzero f d (Nat.le_succ _) p hp
    intro a ha hzero
    subst a
    exact spectrum.zero_notMem ℂ (hA.map Matrix.toLinAlgEquiv') ha
  · have hs := logInterpolation_spectrum_halfOpen f d (Nat.succ_ne_zero _) p hp
    change spectrum ℂ (aeval (Matrix.toLinAlgEquiv' A) p) ⊆ halfOpenStrip at hs
    simpa only [aeval_algHom_apply, AlgEquiv.spectrum_eq] using hs

/-- The same polynomial realizes the principal logarithm on its usual domain. -/
theorem aeval_logHermitePolynomial_eq_principalLog (A : Matrix n n ℂ)
    (hA : HasSlitSpectrum A) : aeval A (logHermitePolynomial A) = principalLog A := by
  rw [aeval_logHermitePolynomial A hA.isUnit, halfOpenLog_eq_principalLog A hA]

theorem logHermitePolynomial_unique (A : Matrix n n ℂ) (hA : IsUnit A) (p : ℂ[X])
    (hp : p.degree < (minpoly ℂ A).degree) (heq : aeval A p = halfOpenLog A) :
    p = logHermitePolynomial A :=
  matrix_polynomial_unique A hp (logHermitePolynomial_degree_lt A)
    (heq.trans (aeval_logHermitePolynomial A hA).symm)

/-- Verification rule for an explicitly supplied logarithm interpolant. -/
theorem halfOpenLog_eq_aeval_of_interpolation (A : Matrix n n ℂ) (hA : IsUnit A) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ A, (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
      p - localLogPolynomial a (Module.finrank ℂ (n → ℂ) + 1)) :
    halfOpenLog A = aeval A p := by
  rw [← aeval_logHermitePolynomial A hA, logHermitePolynomial]
  exact aeval_matrixHermitePolynomial_eq A _ p hp

end SympyProofs.MatrixExponential
