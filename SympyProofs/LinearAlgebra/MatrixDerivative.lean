module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Add
public import SympyProofs.LinearAlgebra.MatrixDerivative.Mul
public import SympyProofs.LinearAlgebra.MatrixDerivative.Pow
public import SympyProofs.LinearAlgebra.MatrixDerivative.Inverse
public import SympyProofs.LinearAlgebra.MatrixDerivative.ZPow

/-! Scalar differentiation of finite real and complex matrices.

* `Basic` identifies `HasDerivAt` with entrywise scalar differentiation and proves
  the affine matrix derivative and differentiation under the trace.
* `Add` proves the matrix sum rule.
* `Mul` proves the ordered product rule for rectangular matrices.
* `Pow` proves the noncommutative natural-power rule.
* `Norms` proves the equivalent first-order remainder criterion for every
  vector-space norm on finite matrices, independently of submultiplicativity.
* `Inverse` proves `(M⁻¹)' = -M⁻¹ * M' * M⁻¹` at invertible matrices, including a
  nonzero-determinant formulation, the affine case `t • X + Z`, and the general
  trace-of-inverse rule, together with entrywise and arbitrary-norm formulations.
* `ZPow` extends the power rule to every integer exponent at nonsingular matrices,
  using a signed interval sum, and also states the negative-power rule explicitly.

Theorems are in `SympyProofs.MatrixDerivative`. They use Mathlib's matrix inverse
and `HasDerivAt`/`deriv`, and impose no commutation assumption on `M` and `M'`.
-/
