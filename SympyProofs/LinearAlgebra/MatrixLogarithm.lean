import SympyProofs.LinearAlgebra.MatrixLogarithm.Logarithm
import SympyProofs.LinearAlgebra.MatrixLogarithm.Nilpotent
import SympyProofs.LinearAlgebra.MatrixLogarithm.InvariantSubspaces
import SympyProofs.LinearAlgebra.MatrixLogarithm.Endomorphism
import SympyProofs.LinearAlgebra.MatrixLogarithm.Interpolation
import SympyProofs.LinearAlgebra.MatrixLogarithm.LocalLogarithm
import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenEndomorphism
import SympyProofs.LinearAlgebra.MatrixLogarithm.PrincipalEndomorphism
import SympyProofs.LinearAlgebra.MatrixLogarithm.PrincipalLogarithm
import SympyProofs.LinearAlgebra.MatrixLogarithm.HalfOpenLogarithm

/-!
# Matrix logarithms

Public entry point for the reusable principal-logarithm infrastructure:

* `Logarithm`: certificates for chosen matrix logarithms and their transformations.
* `Nilpotent`: finite exponential/logarithm inverse laws.
* `InvariantSubspaces`: polynomial intertwining and generalized-eigenspace algebra.
* `Endomorphism`: analytic exponentials and their intertwining laws.
* `Interpolation`: polynomial interpolation of local logarithm expansions.
* `LocalLogarithm`: inverse laws on generalized eigenspaces.
* `HalfOpenEndomorphism`: existence and uniqueness in `-π < im z ≤ π` for
  every invertible complex endomorphism, allowing negative real eigenvalues.
* `PrincipalEndomorphism`: existence and uniqueness for complex endomorphisms.
* `PrincipalLogarithm`: the matrix theorem and transpose/adjoint/conjugation laws.
* `HalfOpenLogarithm`: the matrix theorem for the half-open strip and its
  agreement with the open-strip logarithm wherever both are defined.

`existsUnique_principalLogarithm` proves that `σ(A) ∩ (-∞, 0] = ∅` implies
existence and uniqueness of `L` with `exp L = A` and `σ(L)` in the open strip
`-π < im z < π`. No diagonalizability assumption is used.

`existsUnique_halfOpenLogarithm` instead requires only `IsUnit A` and uses
`-π < im z ≤ π`. In particular, `halfOpenLog_neg_one` proves that the logarithm
of `-I` is `π i I`. The half-open extension does not in general preserve adjoints
or conjugation on the negative real axis.

The functions `principalLog A` and `halfOpenLog A` take no proof arguments.
Their correctness theorems require the corresponding domain hypotheses; outside
those domains the functions return `0`. They are noncomputable mathematical
definitions. The `Logarithm A` certificate constructors still require proofs.

Declarations retain their existing `SympyProofs.MatrixExponential` namespace.
Matrix powers built from these logarithms are in
`SympyProofs.LinearAlgebra.MatrixPower.Basic`,
`SympyProofs.LinearAlgebra.MatrixPower.Principal`, and
`SympyProofs.LinearAlgebra.MatrixPower.HalfOpen`.
-/
