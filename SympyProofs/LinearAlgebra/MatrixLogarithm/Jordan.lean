module

public import SympyProofs.LinearAlgebra.MatrixFunction.JordanBlock
public import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenLogarithm

/-!
# Finite logarithms on Jordan blocks

For `a ≠ 0` and `N^d = 0`, the logarithm of `a I + N` is the finite sum
`log(a) I + ∑ 1 ≤ k < d, (-1)^(k+1) (a⁻¹ N)^k / k`.
It equals the canonical half-open logarithm, including negative eigenvalues.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite block logarithm. The zero-index term vanishes by the division convention. -/
noncomputable def nilpotentBlockLog (a : ℂ) (N : Matrix n n ℂ) (d : ℕ) : Matrix n n ℂ :=
  Complex.log a • 1 + ∑ k ∈ Finset.range d,
    ((-1 : ℚ) ^ (k + 1) / k) • (a⁻¹ • N) ^ k

theorem nilpotentBlockLog_eq_aeval (a : ℂ) (N : Matrix n n ℂ) (d : ℕ) :
    nilpotentBlockLog a N d = aeval (a • 1 + N) (localLogPolynomial a d) := by
  simp only [nilpotentBlockLog, localLogPolynomial, map_add, map_sum, aeval_C]
  simp only [map_rat_smul, map_pow, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, add_sub_cancel_left, smul_mul_assoc, one_mul]

theorem exp_nilpotentBlockLog (a : ℂ) (N : Matrix n n ℂ) (d : ℕ)
    (ha : a ≠ 0) (hN : N ^ d = 0) : exp (nilpotentBlockLog a N d) = a • 1 + N := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [nilpotentBlockLog_eq_aeval, toLin_exp, ← aeval_algHom_apply]
  apply endExp_localLogPolynomial _ a d ha
  simp only [map_add, map_smul, map_one, add_sub_cancel_left, ← map_pow, hN, map_zero]

theorem spectrum_scalar_add_nilpotent (a : ℂ) (N : Matrix n n ℂ) (d : ℕ)
    (hN : N ^ d = 0) : spectrum ℂ (a • 1 + N) ⊆ {a} := by
  nontriviality (Matrix n n ℂ)
  intro b hb
  have hb' : b - a ∈ spectrum ℂ N := by
    have h := spectrum.subset_polynomial_aeval (a • 1 + N) (X - C a) ⟨b, hb, rfl⟩
    simpa only [eval_sub, eval_X, eval_C, map_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, add_sub_cancel_left] using h
  have h := spectrum.pow_mem_pow N d hb'
  rw [hN, spectrum.zero_eq, Set.mem_singleton_iff] at h
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)

theorem spectrum_nilpotentBlockLog (a : ℂ) (N : Matrix n n ℂ) (d : ℕ)
    (hN : N ^ d = 0) : spectrum ℂ (nilpotentBlockLog a N d) ⊆ halfOpenStrip := by
  nontriviality (Matrix n n ℂ)
  rw [nilpotentBlockLog_eq_aeval, spectrum.map_polynomial_aeval_of_nonempty _ _
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (a • 1 + N))]
  rintro _ ⟨b, hb, rfl⟩
  have hb' : b = a := spectrum_scalar_add_nilpotent a N d hN hb
  change (localLogPolynomial a d).eval b ∈ halfOpenStrip
  rw [hb', localLogPolynomial_eval]
  exact log_mem_halfOpenStrip a

theorem halfOpenLog_scalar_add_nilpotent (a : ℂ) (N : Matrix n n ℂ) (d : ℕ)
    (ha : a ≠ 0) (hN : N ^ d = 0) : halfOpenLog (a • 1 + N) = nilpotentBlockLog a N d := by
  symm
  apply halfOpenLog_unique
  · rw [← exp_nilpotentBlockLog a N d ha hN]
    exact isUnit_exp _
  · exact ⟨exp_nilpotentBlockLog a N d ha hN, spectrum_nilpotentBlockLog a N d hN⟩

/-- Direct finite logarithm of an explicit Jordan block. -/
noncomputable def jordanLog (a : ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  nilpotentBlockLog a (jordanShift ℂ m) m

theorem halfOpenLog_jordanBlock (a : ℂ) (m : ℕ) (ha : a ≠ 0) :
    halfOpenLog (jordanBlock a m) = jordanLog a m := by
  rw [jordanBlock, ← Matrix.smul_one_eq_diagonal,
    halfOpenLog_scalar_add_nilpotent a _ m ha (jordanShift_pow_size m)]
  rfl

theorem exp_jordanLog (a : ℂ) (m : ℕ) (ha : a ≠ 0) :
    exp (jordanLog a m) = jordanBlock a m := by
  simpa only [jordanLog, jordanBlock, Matrix.smul_one_eq_diagonal] using
    exp_nilpotentBlockLog a (jordanShift ℂ m) m ha (jordanShift_pow_size m)

theorem isUnit_jordanBlock (a : ℂ) (m : ℕ) (ha : a ≠ 0) : IsUnit (jordanBlock a m) := by
  rw [← exp_jordanLog a m ha]
  exact isUnit_exp _

end SympyProofs.MatrixExponential
