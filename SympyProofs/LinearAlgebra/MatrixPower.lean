import SympyProofs.LinearAlgebra.MatrixPower.Basic
import SympyProofs.LinearAlgebra.MatrixPower.Diagonal
import SympyProofs.LinearAlgebra.MatrixPower.Principal
import SympyProofs.LinearAlgebra.MatrixPower.HalfOpen
import SympyProofs.LinearAlgebra.MatrixPower.General
import SympyProofs.LinearAlgebra.MatrixPower.Compatibility
import SympyProofs.LinearAlgebra.MatrixPower.Singular
import SympyProofs.LinearAlgebra.MatrixPower.Hermitian

/-!
# Matrix powers

Public entry point for complex matrix powers and their identities:

* `General`: `matrixCpow A z`, defined by primary functional calculus for every
  finite complex matrix, including singular and nondiagonalizable matrices.
* `Compatibility`: change of basis, diagonalization, roots, and the ordinary
  integer conjugation/adjoint identities without branch restrictions.
* `Singular`: admissibility at zero and the explicit nilpotent convention.
* `Hermitian`: agreement with the spectral theorem, including singular positive
  semidefinite matrices.
* `Basic`: powers relative to a chosen logarithm and their transformation laws.
* `Diagonal`: entrywise scalar powers on diagonal matrices.
* `Principal`: powers on the slit-spectrum domain, with adjoint/conjugation laws.
* `HalfOpen`: powers for all invertible complex matrices, including negative
  eigenvalues, and the explicit uniqueness theorem `existsUnique_halfOpenCpow`.

Use `matrixCpow A z` for the general power. It agrees with ordinary natural
powers for every matrix, scalar powers on every diagonal matrix, and ordinary
integer powers on invertible matrices. It agrees with `halfOpenCpow` on all
invertible matrices and with `principalCpow` on the slit-spectrum domain.

All three functions take only the matrix and exponent and are noncomputable.
The general definition uses zero Taylor data at a zero eigenvalue for nonnatural
exponents. `MatrixPowerDefined A z` records the admissible domain; outside it,
the value is a totalization convention and need not satisfy root/inverse laws.
The older logarithm-based functions retain their `1` fallback outside their
respective domains; use the compatibility theorems with their hypotheses.

`halfOpenCpow_eq_exp_of_isHalfOpenLogarithm` proves that every logarithm with
spectrum in `-π < im z ≤ π` gives the same power. This fixes the logarithm branch;
it does not assert uniqueness of arbitrary matrix roots.

The general adjoint/conjugation identities are `conjTranspose_matrixCpow` and
`map_star_matrixCpow` on the slit-spectrum domain. Their `natCast` and `intCast`
variants need no branch-cut condition. `matrixCpow_of_diagonalization` and
`matrixCpow_nat_inv_pow_of_diagonalization` include singular matrices.

Declarations retain their existing `SympyProofs.MatrixExponential` namespace.
-/
