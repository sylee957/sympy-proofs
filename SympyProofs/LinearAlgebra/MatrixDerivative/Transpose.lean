module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic

import Mathlib.Analysis.Matrix.Normed

/-! Transposition commutes with scalar differentiation. The parameter field and
the space of matrix entries may differ, allowing real parameters with complex
entries as well as complex parameters. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open scoped Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The derivative of a transpose is the transpose of the derivative. -/
theorem hasDerivAt_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : 𝕜 → Matrix m n E} {M' : Matrix m n E} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => (M s)ᵀ) M'ᵀ t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  exact hasDerivAt_iff_entrywise.mp hM j i

theorem deriv_transpose [Fintype m] [Fintype n]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : 𝕜 → Matrix m n E} {M' : Matrix m n E} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => (M s)ᵀ) t = M'ᵀ := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_transpose hM).deriv

end SympyProofs.MatrixDerivative
