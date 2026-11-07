module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Nilpotent
public import SympyProofs.LinearAlgebra.MatrixFunction.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Polynomial interpolation for the matrix logarithm

The Chinese remainder theorem combines finite logarithm expansions at distinct
eigenvalues. Congruences modulo powers of `X - λ` retain all nilpotent data.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

noncomputable def localLogPolynomial (z : ℂ) (d : ℕ) : ℂ[X] :=
  C (Complex.log z) + ∑ k ∈ Finset.range d,
    ((-1 : ℚ) ^ (k + 1) / k) • (C z⁻¹ * (X - C z)) ^ k

theorem localLogPolynomial_eval (z : ℂ) (d : ℕ) :
    (localLogPolynomial z d).eval z = Complex.log z := by
  simp only [localLogPolynomial, eval_add, eval_C, eval_finsetSum, eval_smul,
    eval_pow, eval_mul, eval_sub, eval_X, sub_self, mul_zero]
  have h : ∀ k : ℕ, ((-1 : ℚ) ^ (k + 1) / k) • (0 : ℂ) ^ k = 0 := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  simp [h]

theorem exists_logInterpolation {s : Set ℂ} (hs : s.Finite) (d : ℕ) :
    ∃ p : ℂ[X], ∀ z ∈ s,
      (X - C z) ^ d ∣ p - localLogPolynomial z d :=
  exists_primaryInterpolation hs d (fun z => localLogPolynomial z d)

theorem aeval_localLogPolynomial {A : Type*} [Ring A] [Algebra ℂ A] [Algebra ℚ A]
    [IsScalarTower ℚ ℂ A]
    (a : A) (z : ℂ) (d : ℕ) (hn : (a - algebraMap ℂ A z) ^ d = 0) :
    aeval a (localLogPolynomial z d) =
      algebraMap ℂ A (Complex.log z) + Nilpotent.log (z⁻¹ • (a - algebraMap ℂ A z)) := by
  have hN : (z⁻¹ • (a - algebraMap ℂ A z)) ^ d = 0 := by
    rw [smul_pow, hn, smul_zero]
  rw [Nilpotent.log_eq_sum hN, localLogPolynomial, map_add, aeval_C, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, map_pow, map_mul, map_sub, aeval_C, aeval_C, aeval_X]
  rw [Algebra.smul_def z⁻¹]

end SympyProofs.MatrixExponential
