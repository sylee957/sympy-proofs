module

public import SympyProofs.LinearAlgebra.MatrixPower.General

/-!
# Matrix exponents

Use the order `exp (log A * B)` for matrix--matrix exponentiation. No
commutativity assumption is needed for the definition. The adjoint reverses
the multiplication order; identifying it with the same convention requires
an additional commutativity hypothesis.

The principal version is specified on the slit-spectrum domain. The half-open
version is specified on all invertible matrices. Their totalized values outside
those domains inherit the logarithm fallback and are not singular matrix powers.

The multiplication order follows Cardoso--Sadeghi, *On the conditioning of the
matrix-matrix exponentiation*, https://arxiv.org/abs/1703.08804.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def principalMatrixPow (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  exp (principalLog A * B)

noncomputable def halfOpenMatrixPow (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  exp (halfOpenLog A * B)

theorem halfOpenMatrixPow_eq_principalMatrixPow (A B : Matrix n n ℂ)
    (hA : HasSlitSpectrum A) : halfOpenMatrixPow A B = principalMatrixPow A B := by
  rw [halfOpenMatrixPow, halfOpenLog_eq_principalLog A hA, principalMatrixPow]

@[simp] theorem principalMatrixPow_scalar (A : Matrix n n ℂ) (z : ℂ) :
    principalMatrixPow A (z • 1) = principalCpow A z := by
  simp only [principalMatrixPow, principalCpow, mul_smul_comm, mul_one]

@[simp] theorem halfOpenMatrixPow_scalar (A : Matrix n n ℂ) (z : ℂ) :
    halfOpenMatrixPow A (z • 1) = halfOpenCpow A z := by
  simp only [halfOpenMatrixPow, halfOpenCpow, mul_smul_comm, mul_one]

theorem halfOpenMatrixPow_scalar_eq_matrixCpow (A : Matrix n n ℂ)
    (hA : IsUnit A) (z : ℂ) : halfOpenMatrixPow A (z • 1) = matrixCpow A z := by
  rw [halfOpenMatrixPow_scalar, matrixCpow_eq_halfOpenCpow A hA]

@[simp] theorem halfOpenMatrixPow_zero (A : Matrix n n ℂ) : halfOpenMatrixPow A 0 = 1 := by
  simp [halfOpenMatrixPow]

@[simp] theorem halfOpenMatrixPow_one (A : Matrix n n ℂ) (hA : IsUnit A) :
    halfOpenMatrixPow A 1 = A := by
  simp [halfOpenMatrixPow, exp_halfOpenLog A hA]

/-- The adjoint reverses the order of the logarithm and the exponent. -/
theorem conjTranspose_principalMatrixPow (A B : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    (principalMatrixPow A B)ᴴ = exp (Bᴴ * principalLog Aᴴ) := by
  rw [principalMatrixPow, ← exp_conjTranspose, Matrix.conjTranspose_mul,
    principalLog_conjTranspose A hA]

theorem conjTranspose_principalMatrixPow_of_commute (A B : Matrix n n ℂ)
    (hA : HasSlitSpectrum A) (hB : Commute (principalLog A) B) :
    (principalMatrixPow A B)ᴴ = principalMatrixPow Aᴴ Bᴴ := by
  rw [conjTranspose_principalMatrixPow A B hA, principalMatrixPow,
    principalLog_conjTranspose A hA]
  congr 1
  simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hB.eq

theorem map_star_principalMatrixPow (A B : Matrix n n ℂ) (hA : HasSlitSpectrum A) :
    (principalMatrixPow A B).map star = principalMatrixPow (A.map star) (B.map star) := by
  rw [principalMatrixPow, ← exp_map_star, principalMatrixPow, principalLog_map_star A hA]
  congr 1
  exact map_mul (starRingEnd ℂ).mapMatrix _ _

/-- Both the base and the exponent transform under the same change of basis. -/
theorem halfOpenMatrixPow_units_conj (P : (Matrix n n ℂ)ˣ) (A B : Matrix n n ℂ)
    (hA : IsUnit A) :
    halfOpenMatrixPow ((P : Matrix n n ℂ) * A * (↑(P⁻¹) : Matrix n n ℂ))
      ((P : Matrix n n ℂ) * B * (↑(P⁻¹) : Matrix n n ℂ)) =
        (P : Matrix n n ℂ) * halfOpenMatrixPow A B * (↑(P⁻¹) : Matrix n n ℂ) := by
  rw [halfOpenMatrixPow, halfOpenLog_units_conj P A hA]
  have he : ((P : Matrix n n ℂ) * halfOpenLog A * (↑(P⁻¹) : Matrix n n ℂ)) *
      ((P : Matrix n n ℂ) * B * (↑(P⁻¹) : Matrix n n ℂ)) =
      (P : Matrix n n ℂ) * (halfOpenLog A * B) * (↑(P⁻¹) : Matrix n n ℂ) := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [he]
  exact Matrix.exp_units_conj P _

/-- Using a basis for the base matrix requires transporting the exponent too. -/
theorem halfOpenMatrixPow_of_similarity (P : (Matrix n n ℂ)ˣ) (J B : Matrix n n ℂ)
    (hJ : IsUnit J) :
    halfOpenMatrixPow ((P : Matrix n n ℂ) * J * (↑(P⁻¹) : Matrix n n ℂ)) B =
      (P : Matrix n n ℂ) *
        halfOpenMatrixPow J ((↑(P⁻¹) : Matrix n n ℂ) * B * (P : Matrix n n ℂ)) *
          (↑(P⁻¹) : Matrix n n ℂ) := by
  have h := halfOpenMatrixPow_units_conj P J
    ((↑(P⁻¹) : Matrix n n ℂ) * B * (P : Matrix n n ℂ)) hJ
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using h

end SympyProofs.MatrixExponential
