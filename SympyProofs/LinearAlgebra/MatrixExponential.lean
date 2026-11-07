import SympyProofs.LinearAlgebra.MatrixExponential.Basic
import SympyProofs.LinearAlgebra.MatrixExponential.Hermite

/-!
# Matrix exponentials

Public entry point for the matrix exponential and its algebraic, transpose,
adjoint, and conjugation laws.
`Hermite` represents the exponential exactly by polynomial evaluation, with
degree below the minimal polynomial and scalar exponential coefficients.

Logarithm definitions and existence/uniqueness theorems are in
`SympyProofs.LinearAlgebra.MatrixLogarithm`. Complex powers and their identities
are in `SympyProofs.LinearAlgebra.MatrixPower`.
-/
