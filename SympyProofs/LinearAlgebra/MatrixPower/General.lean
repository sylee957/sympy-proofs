module

public import SympyProofs.LinearAlgebra.MatrixPower.Endomorphism
public import SympyProofs.LinearAlgebra.MatrixPower.HalfOpen

/-!
# General complex matrix powers

`matrixCpow A z` uses primary functional calculus, including singular matrices.
At nonzero eigenvalues it uses the half-open scalar logarithm branch. At zero,
natural exponents retain the whole polynomial `X^k`; nonnatural exponents use
zero Taylor data. Thus natural powers are correct for every matrix, scalar
powers are correct on every diagonal matrix, and invertible matrices agree
with `halfOpenCpow`.

The function is total and noncomputable. Totality does not assert the existence
of arbitrary roots or inverses of singular matrices. `MatrixPowerDefined`
records the standard admissibility condition at zero.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Primary matrix power, including singular matrices, with zero jets at zero
for nonnatural exponents. No hypotheses are arguments to the definition. -/
noncomputable def matrixCpow (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  Matrix.toLinAlgEquiv'.symm (endCpow (Matrix.toLinAlgEquiv' A) z)

theorem toLin_matrixCpow (A : Matrix n n ℂ) (z : ℂ) :
    Matrix.toLinAlgEquiv' (matrixCpow A z) = endCpow (Matrix.toLinAlgEquiv' A) z :=
  AlgEquiv.apply_symm_apply _ _

/-- Admissibility for the standard primary power. The natural-number alternative
allows every natural power, regardless of the nilpotent blocks at zero.
Otherwise zero blocks of size at most `m` require `m - 1 < re z`.
When zero is absent from the spectrum, the condition is vacuous. -/
def MatrixPowerDefined (A : Matrix n n ℂ) (z : ℂ) : Prop :=
  (∃ k : ℕ, z = (k : ℂ)) ∨
    (0 ∈ spectrum ℂ A → ∃ m : ℕ, 0 < m ∧
      (primaryEnd (Matrix.toLinAlgEquiv' A) 0) ^ m = 0 ∧ (m : ℝ) - 1 < z.re)

theorem MatrixPowerDefined.natCast (A : Matrix n n ℂ) (k : ℕ) :
    MatrixPowerDefined A (k : ℂ) := Or.inl ⟨k, rfl⟩

theorem MatrixPowerDefined.of_isUnit {A : Matrix n n ℂ} (hA : IsUnit A) (z : ℂ) :
    MatrixPowerDefined A z := Or.inr (fun h => (spectrum.zero_notMem ℂ hA h).elim)

/-- Compatibility with ordinary powers, including all singular matrices. -/
@[simp] theorem matrixCpow_natCast (A : Matrix n n ℂ) (k : ℕ) :
    matrixCpow A (k : ℂ) = A ^ k := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [toLin_matrixCpow, endCpow_natCast, map_pow]

@[simp] theorem matrixCpow_zero (A : Matrix n n ℂ) : matrixCpow A 0 = 1 := by
  simpa using matrixCpow_natCast A 0

@[simp] theorem matrixCpow_one (A : Matrix n n ℂ) : matrixCpow A 1 = A := by
  simpa using matrixCpow_natCast A 1

theorem matrixCpow_eq_halfOpenCpow (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    matrixCpow A z = halfOpenCpow A z := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [toLin_matrixCpow, halfOpenCpow, toLin_exp, map_smul]
  apply endCpow_eq_exp_of_halfOpenLogarithm
  · exact hA.map Matrix.toLinAlgEquiv'
  · rw [← toLin_exp, exp_halfOpenLog A hA]
  · simpa only [AlgEquiv.spectrum_eq] using spectrum_halfOpenLog A hA

theorem matrixCpow_eq_principalCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    matrixCpow A z = principalCpow A z := by
  rw [matrixCpow_eq_halfOpenCpow A hA.isUnit, halfOpenCpow_eq_principalCpow A hA]

/-- Integer powers agree whenever the matrix is invertible. -/
theorem matrixCpow_intCast (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℤ) :
    matrixCpow A (k : ℂ) = A ^ k := by
  rw [matrixCpow_eq_halfOpenCpow A hA, halfOpenCpow]
  calc
    exp ((k : ℂ) • halfOpenLog A) = exp (halfOpenLog A) ^ k := by
      simpa only [exp, Int.cast_smul_eq_zsmul] using Matrix.exp_zsmul k (halfOpenLog A)
    _ = A ^ k := by rw [exp_halfOpenLog A hA]

theorem matrixCpow_eq_aeval (A : Matrix n n ℂ) (z : ℂ) (p : ℂ[X])
    (hp : ∀ a ∈ spectrum ℂ A,
      (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
        p - localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1)) :
    matrixCpow A z = aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [toLin_matrixCpow, ← aeval_algHom_apply, endCpow]
  apply primaryFunction_eq_aeval
  simpa only [AlgEquiv.spectrum_eq] using hp

theorem matrixCpow_eq_aeval_primaryPolynomial (A : Matrix n n ℂ) (z : ℂ) :
    matrixCpow A z = aeval A (primaryPolynomial (Matrix.toLinAlgEquiv' A)
      (fun a => localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1))) := by
  apply matrixCpow_eq_aeval
  intro a ha
  apply primaryPolynomial_spec
  simpa only [AlgEquiv.spectrum_eq] using ha

theorem aeval_diagonal_complex (d : n → ℂ) (p : ℂ[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k c =>
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.diagonal_pow, ← Matrix.diagonal_smul]

/-- Diagonal compatibility includes zero entries and all scalar exponents.
For inadmissible exponents at zero, both sides use the same total convention. -/
theorem matrixCpow_diagonal (d : n → ℂ) (z : ℂ) :
    matrixCpow (Matrix.diagonal d) z = diagonalCpow d z := by
  rw [matrixCpow_eq_aeval_primaryPolynomial, aeval_diagonal_complex, diagonalCpow]
  congr 1
  funext i
  rw [primaryPolynomial_eval _ _ (d i) (by
    simpa only [AlgEquiv.spectrum_eq, spectrum_diagonal] using
      (show d i ∈ Set.range d from ⟨i, rfl⟩)), localCpowPolynomial_eval _ _ _ (Nat.succ_ne_zero _)]

/-- Spectral mapping holds for the totalized power as well. -/
theorem spectrum_matrixCpow (A : Matrix n n ℂ) (z : ℂ) :
    spectrum ℂ (matrixCpow A z) = (fun a : ℂ => a ^ z) '' spectrum ℂ A := by
  nontriviality (Matrix n n ℂ)
  rw [matrixCpow_eq_aeval_primaryPolynomial, spectrum.map_polynomial_aeval_of_nonempty _ _
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)]
  apply Set.image_congr
  intro a ha
  rw [primaryPolynomial_eval _ _ a (by simpa only [AlgEquiv.spectrum_eq] using ha),
    localCpowPolynomial_eval _ _ _ (Nat.succ_ne_zero _)]

@[simp] theorem matrixCpow_scalar (a z : ℂ) :
    matrixCpow (a • (1 : Matrix n n ℂ)) z = a ^ z • (1 : Matrix n n ℂ) := by
  simpa only [Matrix.smul_one_eq_diagonal, diagonalCpow] using
    matrixCpow_diagonal (fun _ : n => a) z

@[simp] theorem matrixCpow_zero_matrix (z : ℂ) :
    matrixCpow (0 : Matrix n n ℂ) z = (0 : ℂ) ^ z • (1 : Matrix n n ℂ) := by
  simpa using matrixCpow_scalar (n := n) 0 z

theorem conjTranspose_matrixCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (matrixCpow A z)ᴴ = matrixCpow Aᴴ (star z) := by
  rw [matrixCpow_eq_principalCpow A hA,
    matrixCpow_eq_principalCpow Aᴴ hA.conjTranspose, conjTranspose_principalCpow A hA]

theorem map_star_matrixCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (matrixCpow A z).map star = matrixCpow (A.map star) (star z) := by
  rw [matrixCpow_eq_principalCpow A hA,
    matrixCpow_eq_principalCpow (A.map star) hA.conjugate, map_star_principalCpow A hA]

end SympyProofs.MatrixExponential
