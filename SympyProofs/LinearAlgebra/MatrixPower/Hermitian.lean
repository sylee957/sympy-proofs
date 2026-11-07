module

public import SympyProofs.LinearAlgebra.MatrixPower.Compatibility
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral powers of Hermitian matrices

The general power agrees with the spectral construction, including singular
positive semidefinite matrices. Negative eigenvalues use the same half-open
scalar branch as the rest of the API.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The usual spectral formula for Hermitian matrices, including singular ones. -/
theorem matrixCpow_of_isHermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ) :
    matrixCpow A z = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonalCpow (fun i => (hA.eigenvalues i : ℂ)) z) := by
  let e := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary).toAlgEquiv
  have he : A = e (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) :=
    hA.spectral_theorem
  calc
    matrixCpow A z = matrixCpow (e (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))) z :=
      congrArg (fun B => matrixCpow B z) he
    _ = e (matrixCpow (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) z) :=
      matrixCpow_algEquiv e _ z
    _ = _ := by rw [matrixCpow_diagonal]; rfl

end SympyProofs.MatrixExponential
