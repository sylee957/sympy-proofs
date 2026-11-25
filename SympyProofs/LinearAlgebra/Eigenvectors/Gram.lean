module

public import Mathlib.Analysis.Matrix.Spectrum

/-! # Orthonormal eigenbases of the Gram matrices AᴴA and AAᴴ -/

@[expose] public section

namespace SympyProofs.Diagonalization

open Matrix
open scoped Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The right Gram matrix has an orthonormal eigenbasis for every rectangular A. -/
theorem exists_orthonormal_eigenbasis_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    ∃ (b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (d : n → ℝ),
      ∀ i, (Aᴴ * A) *ᵥ ⇑(b i) = d i • ⇑(b i) := by
  classical
  have h := isHermitian_conjTranspose_mul_self A
  exact ⟨h.eigenvectorBasis, h.eigenvalues, h.mulVec_eigenvectorBasis⟩

/-- The left Gram matrix also has an orthonormal eigenbasis, including at eigenvalue zero. -/
theorem exists_orthonormal_eigenbasis_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    ∃ (b : OrthonormalBasis m 𝕜 (EuclideanSpace 𝕜 m)) (d : m → ℝ),
      ∀ i, (A * Aᴴ) *ᵥ ⇑(b i) = d i • ⇑(b i) := by
  classical
  have h := isHermitian_mul_conjTranspose_self A
  exact ⟨h.eigenvectorBasis, h.eigenvalues, h.mulVec_eigenvectorBasis⟩

end SympyProofs.Diagonalization
