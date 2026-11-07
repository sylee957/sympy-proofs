module

public import SympyProofs.LinearAlgebra.MatrixPower.General

/-!
# Change of basis and algebraic identities for general matrix powers

Primary powers are invariant under change of basis, including singular and
nondiagonalizable matrices. Consequently the diagonal formula applies in any
eigenbasis. Natural and invertible integer powers have unconditional adjoint
and conjugation identities, independently of any branch cut.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Module Polynomial
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrixCpow_algEquiv (e : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (A : Matrix n n ℂ) (z : ℂ) : matrixCpow (e A) z = e (matrixCpow A z) := by
  let p := primaryPolynomial (Matrix.toLinAlgEquiv' A)
    (fun a => localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1))
  have hp : ∀ a ∈ spectrum ℂ A,
      (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
        p - localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1) := by
    intro a ha
    apply primaryPolynomial_spec
    simpa only [AlgEquiv.spectrum_eq] using ha
  rw [matrixCpow_eq_aeval A z p hp,
    matrixCpow_eq_aeval (e A) z p (by simpa only [AlgEquiv.spectrum_eq] using hp)]
  exact aeval_algHom_apply e A p

theorem aeval_units_conj_complex (P : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) (p : ℂ[X]) :
    aeval ((P : Matrix n n ℂ) * A * (↑(P⁻¹) : Matrix n n ℂ)) p =
      (P : Matrix n n ℂ) * aeval A p * (↑(P⁻¹) : Matrix n n ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, Units.conj_pow, mul_smul_comm]

/-- Similarity covariance holds even when the base matrix is singular. -/
theorem matrixCpow_units_conj (P : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) (z : ℂ) :
    matrixCpow ((P : Matrix n n ℂ) * A * (↑(P⁻¹) : Matrix n n ℂ)) z =
      (P : Matrix n n ℂ) * matrixCpow A z * (↑(P⁻¹) : Matrix n n ℂ) := by
  let p := primaryPolynomial (Matrix.toLinAlgEquiv' A)
    (fun a => localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1))
  have hp : ∀ a ∈ spectrum ℂ A,
      (X - C a) ^ (Module.finrank ℂ (n → ℂ) + 1) ∣
        p - localCpowPolynomial a z (Module.finrank ℂ (n → ℂ) + 1) := by
    intro a ha
    apply primaryPolynomial_spec
    simpa only [AlgEquiv.spectrum_eq] using ha
  rw [matrixCpow_eq_aeval A z p hp,
    matrixCpow_eq_aeval _ z p (by simpa only [spectrum.units_conjugate] using hp)]
  exact aeval_units_conj_complex P A p

/-- The usual spectral formula, with no nonzero-eigenvalue assumption. -/
theorem matrixCpow_of_diagonalization (A : Matrix n n ℂ) (P : (Matrix n n ℂ)ˣ)
    (d : n → ℂ) (hA : A = (P : Matrix n n ℂ) * Matrix.diagonal d * (↑(P⁻¹) : Matrix n n ℂ)) (z : ℂ) :
    matrixCpow A z = (P : Matrix n n ℂ) * diagonalCpow d z * (↑(P⁻¹) : Matrix n n ℂ) := by
  rw [hA, matrixCpow_units_conj, matrixCpow_diagonal]

/-- A diagonalizable singular matrix has the selected `q`th root for every
positive natural `q`, just as its scalar eigenvalues do. -/
theorem matrixCpow_nat_inv_pow_of_diagonalization (A : Matrix n n ℂ)
    (P : (Matrix n n ℂ)ˣ) (d : n → ℂ)
    (hA : A = (P : Matrix n n ℂ) * Matrix.diagonal d * (↑(P⁻¹) : Matrix n n ℂ))
    (q : ℕ) (hq : q ≠ 0) : (matrixCpow A ((q : ℂ)⁻¹)) ^ q = A := by
  rw [matrixCpow_of_diagonalization A P d hA, Units.conj_pow, diagonalCpow,
    Matrix.diagonal_pow]
  have hd : (fun i => d i ^ ((q : ℂ)⁻¹)) ^ q = d := by
    funext i
    exact Complex.cpow_nat_inv_pow (d i) hq
  rw [hd]
  exact hA.symm

theorem matrixCpow_add (A : Matrix n n ℂ) (hA : IsUnit A) (z w : ℂ) :
    matrixCpow A (z + w) = matrixCpow A z * matrixCpow A w := by
  simp only [matrixCpow_eq_halfOpenCpow A hA, halfOpenCpow, add_smul]
  exact exp_add_of_commute _ _ (((Commute.refl (halfOpenLog A)).smul_left z).smul_right w)

theorem matrixCpow_neg (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    matrixCpow A (-z) = (matrixCpow A z)⁻¹ := by
  simp only [matrixCpow_eq_halfOpenCpow A hA, halfOpenCpow, neg_smul, exp_neg]

theorem matrixCpow_nat_inv_pow (A : Matrix n n ℂ) (hA : IsUnit A)
    (q : ℕ) (hq : q ≠ 0) : (matrixCpow A ((q : ℂ)⁻¹)) ^ q = A := by
  rw [matrixCpow_eq_halfOpenCpow A hA, halfOpenCpow, ← exp_natCast_smul,
    smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hq), one_smul, exp_halfOpenLog A hA]

theorem conjTranspose_matrixCpow_natCast (A : Matrix n n ℂ) (k : ℕ) :
    (matrixCpow A (k : ℂ))ᴴ = matrixCpow Aᴴ (k : ℂ) := by
  simp only [matrixCpow_natCast, Matrix.conjTranspose_pow]

theorem map_star_matrixCpow_natCast (A : Matrix n n ℂ) (k : ℕ) :
    (matrixCpow A (k : ℂ)).map star = matrixCpow (A.map star) (k : ℂ) := by
  simp only [matrixCpow_natCast]
  change (A ^ k)ᴴᵀ = (Aᴴᵀ) ^ k
  rw [Matrix.conjTranspose_pow, Matrix.transpose_pow]

theorem conjTranspose_matrixCpow_intCast (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℤ) :
    (matrixCpow A (k : ℂ))ᴴ = matrixCpow Aᴴ (k : ℂ) := by
  rw [matrixCpow_intCast A hA, matrixCpow_intCast Aᴴ (by
    simpa only [Matrix.star_eq_conjTranspose] using hA.star), Matrix.conjTranspose_zpow]

theorem map_star_matrixCpow_intCast (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℤ) :
    (matrixCpow A (k : ℂ)).map star = matrixCpow (A.map star) (k : ℂ) := by
  have hc : IsUnit (A.map star) := by
    exact hA.map (starRingEnd ℂ).mapMatrix
  rw [matrixCpow_intCast A hA, matrixCpow_intCast (A.map star) hc]
  change (A ^ k)ᴴᵀ = (Aᴴᵀ) ^ k
  rw [Matrix.conjTranspose_zpow, Matrix.transpose_zpow]

end SympyProofs.MatrixExponential
