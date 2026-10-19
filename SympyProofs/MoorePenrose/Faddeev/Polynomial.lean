import SympyProofs.MoorePenrose.Faddeev.Algorithm
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Specialization of polynomial matrices

Conjugation acts on coefficients and fixes the indeterminate. This convention
is scoped to `Faddeev.PolynomialParameters`. Evaluation at a real parameter
preserves conjugation, so the polynomial numerator and denominator can be
computed before specializing, including where a chosen minor would vanish.
`computePair_eval_isMoorePenrose` needs only the condition that the computed
denominator does not vanish at the parameter; no separate rank hypothesis is
required. Its zeros are exactly the rank-drop locus of the polynomial family.
-/

namespace SympyProofs.MoorePenrose.Faddeev.PolynomialParameters

open Matrix Polynomial

noncomputable section

/-- Coefficientwise conjugation, with the parameter fixed. -/
scoped instance polynomialStarRing {R : Type*} [CommRing R] [StarRing R] :
    StarRing R[X] where
  star p := p.map (starRingEnd R)
  star_involutive p := by
    ext k
    simp
  star_mul p q := by simp [Polynomial.map_mul, mul_comm]
  star_add p q := by simp

@[simp] theorem star_X {R : Type*} [CommRing R] [StarRing R] :
    star (X : R[X]) = X := by
  change Polynomial.map (starRingEnd R) X = X
  simp

@[simp] theorem star_C {R : Type*} [CommRing R] [StarRing R] (r : R) :
    star (C r) = C (star r) := by
  change Polynomial.map (starRingEnd R) (C r) = C (star r)
  simp [starRingEnd_apply]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Polynomial evaluation viewed as a rational-algebra homomorphism. -/
noncomputable def evaluation (x : 𝕜) : 𝕜[X] →ₐ[ℚ] 𝕜 :=
  (Polynomial.aeval x).restrictScalars ℚ

/-- Evaluation commutes with coefficient conjugation at a real parameter. -/
theorem evaluation_star (x : 𝕜) (hx : star x = x) (p : 𝕜[X]) :
    evaluation x (star p) = star (evaluation x p) := by
  change (p.map (starRingEnd 𝕜)).eval x = star (p.eval x)
  simpa only [starRingEnd_apply, hx] using
    (Polynomial.eval_map_apply (f := starRingEnd 𝕜) (p := p) x)

/-- Symbolic computation remains valid at every real specialization of rank `r`. -/
theorem specialize_real {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜[X]) (r : ℕ) (t : ℝ)
    (hr : (A.map (evaluation (t : 𝕜))).rank = r) :
    evaluation (t : 𝕜) (denominator A r) ≠ 0 ∧
      IsMoorePenrose (A.map (evaluation (t : 𝕜)))
        ((evaluation (t : 𝕜) (denominator A r))⁻¹ •
          (numerator A r).map (evaluation (t : 𝕜))) := by
  exact specialization_correct (evaluation (t : 𝕜))
    (evaluation_star _ (by simp)) A r hr

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq 𝕜]

/-- For the symbolic output `(N, d)`, the formula `d(t)⁻¹ • N(t)` is the
Moore–Penrose pseudoinverse of `A(t)` whenever `d(t) ≠ 0`. -/
theorem computePair_eval_isMoorePenrose (A : Matrix m n 𝕜[X]) (t : ℝ)
    (hd : (computePair A).2.eval (t : 𝕜) ≠ 0) :
    IsMoorePenrose (A.map (Polynomial.eval (t : 𝕜)))
      (((computePair A).2.eval (t : 𝕜))⁻¹ •
        (computePair A).1.map (Polynomial.eval (t : 𝕜))) := by
  exact computePair_specialization_of_denominator_ne_zero (evaluation (t : 𝕜))
    (evaluation_star _ (by simp)) A hd

/-- `d(t) ≠ 0` is equivalent to preserving the rank selected by the symbolic scan. -/
theorem computePair_eval_denominator_ne_zero_iff (A : Matrix m n 𝕜[X]) (t : ℝ) :
    (computePair A).2.eval (t : 𝕜) ≠ 0 ↔
      (A.map (Polynomial.eval (t : 𝕜))).rank =
        rankUpTo (Aᴴ * A) (Fintype.card n) := by
  exact computePair_specialization_denominator_ne_zero_iff (evaluation (t : 𝕜))
    (evaluation_star _ (by simp)) A

/-- `d(t) = 0` is exactly the condition that `A(t)` has dropped below the
rank selected by the symbolic scan. The symbolic pair is evaluated, not recomputed. -/
theorem computePair_eval_denominator_eq_zero_iff (A : Matrix m n 𝕜[X]) (t : ℝ) :
    (computePair A).2.eval (t : 𝕜) = 0 ↔
      (A.map (Polynomial.eval (t : 𝕜))).rank <
        rankUpTo (Aᴴ * A) (Fintype.card n) := by
  exact computePair_specialization_denominator_eq_zero_iff (evaluation (t : 𝕜))
    (evaluation_star _ (by simp)) A

end

end SympyProofs.MoorePenrose.Faddeev.PolynomialParameters
