module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Add
public import SympyProofs.LinearAlgebra.MatrixDerivative.Mul
public import SympyProofs.LinearAlgebra.MatrixDerivative.Pow
public import SympyProofs.LinearAlgebra.MatrixDerivative.Trace
public import SympyProofs.LinearAlgebra.MatrixDerivative.Determinant
public import SympyProofs.LinearAlgebra.MatrixDerivative.Permanent
public import SympyProofs.LinearAlgebra.MatrixDerivative.Kronecker
public import SympyProofs.LinearAlgebra.MatrixDerivative.Hadamard
public import SympyProofs.LinearAlgebra.MatrixDerivative.Transpose
public import SympyProofs.LinearAlgebra.MatrixDerivative.Conjugate
public import SympyProofs.LinearAlgebra.MatrixDerivative.Adjoint
public import SympyProofs.LinearAlgebra.MatrixDerivative.Inverse
public import SympyProofs.LinearAlgebra.MatrixDerivative.ZPow

/-! Scalar differentiation of finite real and complex matrices.

* `Basic` identifies `HasDerivAt` with entrywise scalar differentiation and proves
  the affine matrix derivative. The entrywise characterization allows different
  parameter and entry spaces, including real parameters with complex entries.
* `Add` proves the matrix sum rule.
* `Mul` proves the ordered product rule for rectangular matrices.
* `Pow` proves the noncommutative natural-power rule.
* `Trace` proves that taking the trace commutes with scalar differentiation.
* `Determinant` proves the column replacement rule and Jacobi's adjugate formula,
  as well as its inverse formulation at nonsingular matrices.
* `Permanent` proves the trace formula and column replacement rule for square-matrix
  permanents, using the algebraic definitions in `LinearAlgebra.Permanent`.
* `Kronecker` proves the ordered product rule for Kronecker products.
* `Hadamard` proves the product rule for entrywise Hadamard products.
* `Transpose` proves that transposition commutes with scalar differentiation.
* `Conjugate` and `Adjoint` prove the entrywise-conjugation and conjugate-transpose
  rules for differentiation by a real parameter. For complex-differentiable matrix
  functions, they characterize complex differentiability after these operations
  by the vanishing of the original derivative.
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
