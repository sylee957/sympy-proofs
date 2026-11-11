module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of Kronecker products of rectangular matrices.
The product rule preserves the order of the factors. Its `HasDerivAt` statement
allows arbitrary index types, using the product topology on matrices. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped Kronecker

variable {𝕜 m n p q : Type*} [RCLike 𝕜]

/-- The product rule for the Kronecker product, proved entrywise. -/
theorem hasDerivAt_kronecker
    {A : 𝕜 → Matrix m n 𝕜} {B : 𝕜 → Matrix p q 𝕜}
    {A' : Matrix m n 𝕜} {B' : Matrix p q 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s ⊗ₖ B s) (A' ⊗ₖ B t + A t ⊗ₖ B') t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  simpa only [Matrix.kroneckerMap_apply, Matrix.add_apply, Pi.mul_apply] using!
    (hasDerivAt_iff_entrywise.mp hA i.1 j.1).mul
      (hasDerivAt_iff_entrywise.mp hB i.2 j.2)

theorem deriv_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    {A : 𝕜 → Matrix m n 𝕜} {B : 𝕜 → Matrix p q 𝕜}
    {A' : Matrix m n 𝕜} {B' : Matrix p q 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    deriv (fun s => A s ⊗ₖ B s) t = A' ⊗ₖ B t + A t ⊗ₖ B' := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_kronecker hA hB).deriv

end SympyProofs.MatrixDerivative
