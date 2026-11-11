module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of natural powers of finite square matrices.
The power rule preserves the order of the matrix factors. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- Differentiating a natural power replaces one factor at a time by `M'`.
For `k = 0`, the empty sum gives the zero derivative of the identity matrix. -/
theorem hasDerivAt_pow [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (k : ℕ) :
    HasDerivAt (fun s => M s ^ k)
      (∑ i ∈ Finset.range k, M t ^ (k - 1 - i) * M' * M t ^ i) t := by
  open scoped Matrix.Norms.Operator in
    simpa only [Nat.pred_eq_sub_one] using! hM.fun_pow' k

theorem deriv_pow [Fintype n] [DecidableEq n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) (k : ℕ) :
    deriv (fun s => M s ^ k) t =
      ∑ i ∈ Finset.range k, M t ^ (k - 1 - i) * M' * M t ^ i := by
  open scoped Matrix.Norms.Operator in
    simpa using! (hasDerivAt_pow hM k).deriv

end SympyProofs.MatrixDerivative
