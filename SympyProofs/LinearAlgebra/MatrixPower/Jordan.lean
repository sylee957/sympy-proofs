module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Jordan
public import SympyProofs.LinearAlgebra.MatrixPower.MatrixExponent

/-!
# Powers directly on Jordan blocks

`jordanCpow` evaluates the finite local power polynomial and includes zero
eigenvalues with the same convention as `matrixCpow`.

For a matrix exponent, `jordanMatrixPow a B` exponentiates the product of the
finite Jordan logarithm with `B`. Its correctness requires `a ≠ 0`, but no
commutativity of `B` with the block. The final exponential cannot generally
be truncated: multiplying a nilpotent matrix by an arbitrary `B` need not
give a nilpotent matrix.

Under similarity, the exponent must also be transported into the Jordan
basis. For several blocks, an arbitrary exponent can mix the blocks; this
is not an independent block-by-block operation in general.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open Polynomial

/-- Direct finite-polynomial scalar power of a Jordan block, including `a = 0`. -/
noncomputable def jordanCpow (a z : ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  aeval (jordanBlock a m) (localCpowPolynomial a z (m + 1))

theorem jordanCpow_eq_matrixCpow (a z : ℂ) (m : ℕ) :
    jordanCpow a z m = matrixCpow (jordanBlock a m) z := by
  symm
  apply matrixCpow_eq_aeval
  intro b hb
  have hb' : b = a := spectrum_scalar_add_nilpotent a (jordanShift ℂ m) m
    (jordanShift_pow_size m) (by simpa only [jordanBlock, Matrix.smul_one_eq_diagonal] using hb)
  simp only [hb', Module.finrank_fintype_fun_eq_card, Fintype.card_fin, sub_self, dvd_zero]

@[simp] theorem jordanCpow_natCast (a : ℂ) (k m : ℕ) :
    jordanCpow a (k : ℂ) m = jordanBlock a m ^ k := by
  rw [jordanCpow_eq_matrixCpow, matrixCpow_natCast]

variable {m : ℕ}

/-- Matrix exponent directly on a Jordan block, using `exp (jordanLog a m * B)`.
The specification requires a nonzero eigenvalue. -/
noncomputable def jordanMatrixPow (a : ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := exp (jordanLog a m * B)

theorem jordanMatrixPow_eq_exp_sum (a : ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    jordanMatrixPow a B = exp ((Complex.log a • 1 + ∑ k ∈ Finset.range m,
      ((-1 : ℚ) ^ (k + 1) / k) • (a⁻¹ • jordanShift ℂ m) ^ k) * B) := rfl

theorem jordanMatrixPow_eq_halfOpenMatrixPow (a : ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (ha : a ≠ 0) : jordanMatrixPow a B = halfOpenMatrixPow (jordanBlock a m) B := by
  rw [halfOpenMatrixPow, halfOpenLog_jordanBlock a m ha, jordanMatrixPow]

theorem jordanMatrixPow_eq_principalMatrixPow (a : ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (ha : a ∈ Complex.slitPlane) :
    jordanMatrixPow a B = principalMatrixPow (jordanBlock a m) B := by
  rw [jordanMatrixPow_eq_halfOpenMatrixPow a B (Complex.slitPlane_ne_zero ha)]
  apply halfOpenMatrixPow_eq_principalMatrixPow
  intro b hb
  have hb' : b = a := spectrum_scalar_add_nilpotent a (jordanShift ℂ m) m
    (jordanShift_pow_size m) (by simpa only [jordanBlock, Matrix.smul_one_eq_diagonal] using hb)
  simpa only [hb'] using ha

theorem jordanMatrixPow_scalar (a z : ℂ) (ha : a ≠ 0) :
    jordanMatrixPow a (z • (1 : Matrix (Fin m) (Fin m) ℂ)) = jordanCpow a z m := by
  rw [jordanMatrixPow_eq_halfOpenMatrixPow a _ ha,
    halfOpenMatrixPow_scalar_eq_matrixCpow _ (isUnit_jordanBlock a m ha),
    jordanCpow_eq_matrixCpow]

@[simp] theorem jordanMatrixPow_zero (a : ℂ) :
    jordanMatrixPow a (0 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  simp [jordanMatrixPow]

theorem jordanMatrixPow_one (a : ℂ) (ha : a ≠ 0) :
    jordanMatrixPow a (1 : Matrix (Fin m) (Fin m) ℂ) = jordanBlock a m := by
  simp only [jordanMatrixPow, mul_one, exp_jordanLog a m ha]

/-- A direct Jordan-block calculation in an arbitrary basis. The exponent is
`P⁻¹ B P` in the block's basis, rather than the original `B`. -/
theorem halfOpenMatrixPow_jordan_similarity (a : ℂ) (ha : a ≠ 0)
    (P : (Matrix (Fin m) (Fin m) ℂ)ˣ) (B : Matrix (Fin m) (Fin m) ℂ) :
    halfOpenMatrixPow ((P : Matrix (Fin m) (Fin m) ℂ) * jordanBlock a m *
      (↑(P⁻¹) : Matrix (Fin m) (Fin m) ℂ)) B =
      (P : Matrix (Fin m) (Fin m) ℂ) *
        jordanMatrixPow a ((↑(P⁻¹) : Matrix (Fin m) (Fin m) ℂ) * B *
          (P : Matrix (Fin m) (Fin m) ℂ)) * (↑(P⁻¹) : Matrix (Fin m) (Fin m) ℂ) := by
  rw [halfOpenMatrixPow_of_similarity P _ B (isUnit_jordanBlock a m ha),
    jordanMatrixPow_eq_halfOpenMatrixPow a _ ha]

end SympyProofs.MatrixExponential
