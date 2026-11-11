module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of Hadamard products of matrices of the same shape.
The `HasDerivAt` product rule allows arbitrary index types, using the product
topology on matrices. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The product rule for the entrywise Hadamard product. -/
theorem hasDerivAt_hadamard {A B : 𝕜 → Matrix m n 𝕜}
    {A' B' : Matrix m n 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s ⊙ B s) (A' ⊙ B t + A t ⊙ B') t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  simpa only [Matrix.hadamard_apply, Matrix.add_apply, Pi.mul_apply] using!
    (hasDerivAt_iff_entrywise.mp hA i j).mul (hasDerivAt_iff_entrywise.mp hB i j)

theorem deriv_hadamard [Fintype m] [Fintype n] {A B : 𝕜 → Matrix m n 𝕜}
    {A' B' : Matrix m n 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    deriv (fun s => A s ⊙ B s) t = A' ⊙ B t + A t ⊙ B' := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_hadamard hA hB).deriv

end SympyProofs.MatrixDerivative
