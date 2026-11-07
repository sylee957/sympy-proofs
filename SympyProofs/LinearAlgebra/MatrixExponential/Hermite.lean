module

public import SympyProofs.LinearAlgebra.MatrixFunction.Hermite
public import SympyProofs.LinearAlgebra.MatrixLogarithm.Endomorphism

/-!
# Exact polynomial representations of matrix exponentials

The exponential Taylor data at `a` are `exp(a) / k!`. Hermite interpolation
and reduction modulo the minimal polynomial produce a finite polynomial whose
evaluation is exactly the analytic matrix exponential, including defective
and singular matrices. Only scalar exponentials occur in its coefficients.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial

/-- The finite exponential Taylor polynomial about `a`. -/
noncomputable def localExpPolynomial (a : ℂ) (d : ℕ) : ℂ[X] :=
  C (Complex.exp a) * ∑ k ∈ Finset.range d, (k.factorial : ℚ)⁻¹ • (X - C a) ^ k

section Endomorphism

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]

theorem aeval_localExpPolynomial (f : End ℂ V) (a : ℂ) (d : ℕ)
    (hn : (f - a • 1) ^ d = 0) : aeval f (localExpPolynomial a d) = endExp f := by
  rw [endExp_eq_of_shift_nilpotent f a ⟨d, hn⟩, IsNilpotent.exp_eq_sum hn]
  simp only [localExpPolynomial, map_mul, map_sum, aeval_C, map_rat_smul,
    map_pow, map_sub, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem primaryFunction_localExpPolynomial (f : End ℂ V) :
    primaryFunction f (fun a => localExpPolynomial a (Module.finrank ℂ V + 1)) = endExp f := by
  symm
  apply primaryFunction_unique
  intro a ha
  rw [aeval_localExpPolynomial _ _ _
    (pow_eq_zero_of_le ((Submodule.finrank_le _).trans (Nat.le_succ _))
      (nilpotent_pow_finrank (primaryEnd_nilpotent f a)))]
  exact endExp_intertwine _ (primaryEnd_intertwine f a)

end Endomorphism

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An exact polynomial for `exp A`, reduced modulo `minpoly ℂ A`. -/
noncomputable def expHermitePolynomial (A : Matrix n n ℂ) : ℂ[X] :=
  matrixHermitePolynomial A (fun a => localExpPolynomial a (Module.finrank ℂ (n → ℂ) + 1))

theorem expHermitePolynomial_degree_lt (A : Matrix n n ℂ) :
    (expHermitePolynomial A).degree < (minpoly ℂ A).degree :=
  matrixHermitePolynomial_degree_lt A _

/-- The finite polynomial formula is exact, with no convergence approximation. -/
theorem aeval_expHermitePolynomial (A : Matrix n n ℂ) :
    aeval A (expHermitePolynomial A) = exp A := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [expHermitePolynomial, toLin_aeval_matrixHermitePolynomial,
    primaryFunction_localExpPolynomial, toLin_exp]

theorem expHermitePolynomial_unique (A : Matrix n n ℂ) (p : ℂ[X])
    (hp : p.degree < (minpoly ℂ A).degree) (heq : aeval A p = exp A) :
    p = expHermitePolynomial A :=
  matrix_polynomial_unique A hp (expHermitePolynomial_degree_lt A)
    (heq.trans (aeval_expHermitePolynomial A).symm)

/-- Verification rule for an explicitly supplied exponential interpolant. -/
theorem exp_eq_aeval_of_interpolation (A : Matrix n n ℂ) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ A, (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
      p - localExpPolynomial a (Module.finrank ℂ (n → ℂ) + 1)) : exp A = aeval A p := by
  rw [← aeval_expHermitePolynomial, expHermitePolynomial]
  exact aeval_matrixHermitePolynomial_eq A _ p hp

end SympyProofs.MatrixExponential
