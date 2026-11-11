module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! Scalar derivatives of the trace of finite square matrices. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- Taking the trace commutes with differentiation by a scalar. -/
theorem hasDerivAt_trace [Fintype n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    HasDerivAt (fun s => Matrix.trace (M s)) (Matrix.trace M') t := by
  change HasDerivAt (fun s => ∑ i, M s i i) (∑ i, M' i i) t
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_iff_entrywise.mp hM i i)

theorem deriv_trace [Fintype n]
    {M : 𝕜 → Matrix n n 𝕜} {M' : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M M' t) :
    deriv (fun s => Matrix.trace (M s)) t = Matrix.trace M' :=
  (hasDerivAt_trace hM).deriv

end SympyProofs.MatrixDerivative
