module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of matrix products. The product rule preserves the order
of the factors and requires only the inner index type to be finite. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 m n p : Type*} [RCLike 𝕜]

/-- The ordered product rule for compatible rectangular matrices. -/
theorem hasDerivAt_mul [Fintype n]
    {A : 𝕜 → Matrix m n 𝕜} {B : 𝕜 → Matrix n p 𝕜}
    {A' : Matrix m n 𝕜} {B' : Matrix n p 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using!
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_iff_entrywise.mp hA i k).mul (hasDerivAt_iff_entrywise.mp hB k j))

theorem deriv_mul [Fintype m] [Fintype n] [Fintype p]
    {A : 𝕜 → Matrix m n 𝕜} {B : 𝕜 → Matrix n p 𝕜}
    {A' : Matrix m n 𝕜} {B' : Matrix n p 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    deriv (fun s => A s * B s) t = A' * B t + A t * B' := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_mul hA hB).deriv

end SympyProofs.MatrixDerivative
