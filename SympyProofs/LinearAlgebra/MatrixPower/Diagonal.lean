module

public import SympyProofs.LinearAlgebra.MatrixExponential.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Principal powers of diagonal matrices

`diagonalCpow` applies the principal scalar power to each diagonal entry. For
nonzero entries it agrees with the exponential of the scaled diagonal logarithm.
The conjugation and adjoint identities require the entries to avoid the negative
real axis, expressed by `arg ≠ π`.

The general logarithm theorems are in `MatrixLogarithm.PrincipalLogarithm` and
`MatrixLogarithm.HalfOpenLogarithm`. Agreement with the half-open matrix power
for nonzero diagonal entries is proved in `MatrixPower.HalfOpen`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [DecidableEq n]

/-- Principal complex powers of a diagonal matrix, including scalar powers at zero. -/
noncomputable def diagonalCpow (d : n → ℂ) (z : ℂ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => d i ^ z)

section Conjugation

/-- The principal-power adjoint identity with the branch-cut hypothesis explicit. -/
theorem conjTranspose_diagonalCpow (d : n → ℂ) (z : ℂ)
    (hd : ∀ i, (d i).arg ≠ Real.pi) :
    (diagonalCpow d z)ᴴ = diagonalCpow (fun i => star (d i)) (star z) := by
  rw [diagonalCpow, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simpa using (Complex.conj_cpow (d i) (star z) (hd i)).symm

theorem map_star_diagonalCpow (d : n → ℂ) (z : ℂ)
    (hd : ∀ i, (d i).arg ≠ Real.pi) :
    (diagonalCpow d z).map star = diagonalCpow (fun i => star (d i)) (star z) := by
  rw [diagonalCpow, Matrix.map_diagonal_star]
  simpa only [diagonalCpow, Matrix.diagonal_conjTranspose] using
    conjTranspose_diagonalCpow d z hd

end Conjugation

section Exponential

variable [Fintype n]

/-- For nonzero diagonal entries, principal powers are exponentials of the
principal diagonal logarithm scaled by the exponent. -/
theorem diagonalCpow_eq_exp (d : n → ℂ) (z : ℂ) (hd : ∀ i, d i ≠ 0) :
    diagonalCpow d z = exp (z • Matrix.diagonal (fun i => Complex.log (d i))) := by
  rw [diagonalCpow, ← Matrix.diagonal_smul, exp_diagonal_complex]
  congr 1
  funext i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
    Complex.cpow_def_of_ne_zero (hd i) z

end Exponential

end SympyProofs.MatrixExponential
