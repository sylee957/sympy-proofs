module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.PrincipalLogarithm
public import SympyProofs.LinearAlgebra.MatrixPower.Basic

/-!
# Principal complex powers of arbitrary finite matrices

For matrices with spectrum avoiding `(-∞, 0]`, define `A^z = exp (z • Log A)`.
The principal logarithm theorem proves the branch compatibility needed for
adjoint and entrywise conjugation. Both identities conjugate the exponent.

The function takes only `A` and `z`. Its correctness theorems carry the domain
hypothesis. Outside the slit-spectrum domain, `principalLog A = 0`, so this
total definition returns `1`; that fallback is not a matrix-power specification.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex matrix power on the slit-spectrum domain, with value `1` elsewhere. -/
noncomputable def principalCpow (A : Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ := exp (z • principalLog A)

theorem principalCpow_eq_exp (A : Matrix n n ℂ) (z : ℂ) :
    principalCpow A z = exp (z • principalLog A) := rfl

theorem principalCpow_of_not_hasSlitSpectrum (A : Matrix n n ℂ)
    (hA : ¬HasSlitSpectrum A) (z : ℂ) : principalCpow A z = 1 := by
  rw [principalCpow, principalLog_of_not_hasSlitSpectrum A hA, smul_zero, exp_zero]

theorem principalCpow_eq_cpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    principalCpow A z = (principalLogarithm A hA).cpow z := rfl

@[simp] theorem principalCpow_zero (A : Matrix n n ℂ) :
    principalCpow A 0 = 1 := by simp [principalCpow]

@[simp] theorem principalCpow_one (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    principalCpow A 1 = A := by simp [principalCpow, exp_principalLog A hA]

theorem principalCpow_natCast (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (k : ℕ) :
    principalCpow A (k : ℂ) = A ^ k := by
  rw [principalCpow, exp_natCast_smul, exp_principalLog A hA]

theorem transpose_principalCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (principalCpow A z)ᵀ = principalCpow Aᵀ z := by
  simp only [principalCpow, principalLog_transpose A hA, ← exp_transpose, Matrix.transpose_smul]

/-- `(A^z)ᴴ = (Aᴴ)^(conj z)` for principal powers on the slit-spectrum domain. -/
theorem conjTranspose_principalCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (principalCpow A z)ᴴ = principalCpow Aᴴ (star z) := by
  rw [principalCpow, conjTranspose_exp_smul, principalCpow, principalLog_conjTranspose A hA]

/-- Entrywise conjugation also conjugates the scalar exponent. -/
theorem map_star_principalCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (principalCpow A z).map star =
      principalCpow (A.map star) (star z) := by
  rw [principalCpow, map_star_exp_smul, principalCpow, principalLog_map_star A hA]

end SympyProofs.MatrixExponential
