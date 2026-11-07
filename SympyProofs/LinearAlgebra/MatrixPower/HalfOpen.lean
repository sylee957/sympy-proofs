module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenLogarithm
public import SympyProofs.LinearAlgebra.MatrixPower.Principal
public import SympyProofs.LinearAlgebra.MatrixPower.Diagonal

/-!
# Complex powers on the half-open logarithm branch

`halfOpenCpow A z` takes only the matrix and exponent. Its power specification
holds for every invertible complex matrix, including matrices with negative
eigenvalues. It agrees with `principalCpow` on the slit-spectrum domain and
with scalar principal powers on invertible diagonal matrices. On singular
matrices the zero-logarithm fallback makes its value `1`; no power specification
is claimed there. The definitions are noncomputable, not numerical algorithms.

`halfOpenCpow_eq_exp_of_isHalfOpenLogarithm` identifies the result for any
logarithm satisfying the branch condition. `existsUnique_halfOpenCpow` states
existence and uniqueness with that condition explicit.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix powers on the half-open logarithm branch, with value `1` on singular matrices. -/
noncomputable def halfOpenCpow (A : Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ := exp (z • halfOpenLog A)

theorem halfOpenCpow_eq_exp (A : Matrix n n ℂ) (z : ℂ) :
    halfOpenCpow A z = exp (z • halfOpenLog A) := rfl

theorem halfOpenCpow_of_not_isUnit (A : Matrix n n ℂ) (hA : ¬IsUnit A) (z : ℂ) :
    halfOpenCpow A z = 1 := by
  rw [halfOpenCpow, halfOpenLog_of_not_isUnit A hA, smul_zero, exp_zero]

/-- Every logarithm satisfying the half-open branch condition gives the same power. -/
theorem halfOpenCpow_eq_exp_of_isHalfOpenLogarithm (A : Matrix n n ℂ) (hA : IsUnit A)
    (z : ℂ) (L : Matrix n n ℂ) (hL : IsHalfOpenLogarithm A L) :
    halfOpenCpow A z = exp (z • L) := by
  rw [halfOpenLog_unique A L hA hL]
  rfl

/-- A matrix power obtained from a logarithm with spectrum in `-π < im z ≤ π`. -/
def IsHalfOpenCpow (A : Matrix n n ℂ) (z : ℂ) (B : Matrix n n ℂ) : Prop :=
  ∃ L, IsHalfOpenLogarithm A L ∧ B = exp (z • L)

theorem halfOpenCpow_spec (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    IsHalfOpenCpow A z (halfOpenCpow A z) :=
  ⟨halfOpenLog A, halfOpenLog_spec A hA, rfl⟩

theorem halfOpenCpow_unique (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ)
    {B : Matrix n n ℂ} (hB : IsHalfOpenCpow A z B) : B = halfOpenCpow A z := by
  obtain ⟨L, hL, rfl⟩ := hB
  exact (halfOpenCpow_eq_exp_of_isHalfOpenLogarithm A hA z L hL).symm

/-- Fixing the half-open logarithm branch uniquely determines the matrix power.
This does not assert uniqueness of arbitrary solutions to a matrix root equation. -/
theorem existsUnique_halfOpenCpow (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    ∃! B : Matrix n n ℂ, IsHalfOpenCpow A z B :=
  ⟨halfOpenCpow A z, halfOpenCpow_spec A hA z, fun _ hB => halfOpenCpow_unique A hA z hB⟩

theorem halfOpenCpow_eq_cpow (A : Matrix n n ℂ) (hA : IsUnit A) (z : ℂ) :
    halfOpenCpow A z = (halfOpenLogarithm A hA).cpow z := rfl

@[simp] theorem halfOpenCpow_zero (A : Matrix n n ℂ) :
    halfOpenCpow A 0 = 1 := by simp [halfOpenCpow]

@[simp] theorem halfOpenCpow_one (A : Matrix n n ℂ) (hA : IsUnit A) :
    halfOpenCpow A 1 = A := by simp [halfOpenCpow, exp_halfOpenLog A hA]

theorem halfOpenCpow_natCast (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℕ) :
    halfOpenCpow A (k : ℂ) = A ^ k := by
  rw [halfOpenCpow, exp_natCast_smul, exp_halfOpenLog A hA]

theorem halfOpenCpow_eq_principalCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    halfOpenCpow A z = principalCpow A z := by
  rw [halfOpenCpow, halfOpenLog_eq_principalLog A hA, principalCpow]

/-- The slit-spectrum condition suffices for the adjoint identity at every exponent.
Integer exponents allow negative eigenvalues; see `MatrixPower.Compatibility`. -/
theorem conjTranspose_halfOpenCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (halfOpenCpow A z)ᴴ = halfOpenCpow Aᴴ (star z) := by
  rw [halfOpenCpow_eq_principalCpow A hA,
    halfOpenCpow_eq_principalCpow Aᴴ hA.conjTranspose, conjTranspose_principalCpow A hA]

/-- Entrywise conjugation under the same sufficient spectral condition. -/
theorem map_star_halfOpenCpow (A : Matrix n n ℂ) (hA : HasSlitSpectrum A) (z : ℂ) :
    (halfOpenCpow A z).map star =
      halfOpenCpow (A.map star) (star z) := by
  rw [halfOpenCpow_eq_principalCpow A hA,
    halfOpenCpow_eq_principalCpow (A.map star) hA.conjugate, map_star_principalCpow A hA]

theorem halfOpenCpow_diagonal (d : n → ℂ) (hA : IsUnit (Matrix.diagonal d)) (z : ℂ) :
    halfOpenCpow (Matrix.diagonal d) z = diagonalCpow d z := by
  rw [halfOpenCpow, halfOpenLog_diagonal d hA]
  symm
  apply diagonalCpow_eq_exp
  intro i hi
  apply spectrum.zero_notMem ℂ hA
  rw [spectrum_diagonal]
  exact ⟨i, hi⟩

/-- The negative scalar matrix has powers for every complex exponent. -/
theorem halfOpenCpow_neg_one (z : ℂ) :
    halfOpenCpow (-1 : Matrix n n ℂ) z =
      Complex.exp (z * (Real.pi * Complex.I)) • (1 : Matrix n n ℂ) := by
  rw [halfOpenCpow, halfOpenLog_neg_one, smul_smul, Matrix.smul_one_eq_diagonal,
    exp_diagonal_complex, Matrix.smul_one_eq_diagonal]

end SympyProofs.MatrixExponential
