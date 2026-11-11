module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of matrix sums. The sum rule allows arbitrary index types. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- Matrix addition is differentiated entrywise. -/
theorem hasDerivAt_add {A B : 𝕜 → Matrix m n 𝕜}
    {A' B' : Matrix m n 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s + B s) (A' + B') t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  exact (hasDerivAt_iff_entrywise.mp hA i j).add
    (hasDerivAt_iff_entrywise.mp hB i j)

theorem deriv_add [Fintype m] [Fintype n] {A B : 𝕜 → Matrix m n 𝕜}
    {A' B' : Matrix m n 𝕜} {t : 𝕜}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    deriv (fun s => A s + B s) t = A' + B' := by
  open scoped Matrix.Norms.Elementwise in
    simpa using! (hasDerivAt_add hA hB).deriv

end SympyProofs.MatrixDerivative
