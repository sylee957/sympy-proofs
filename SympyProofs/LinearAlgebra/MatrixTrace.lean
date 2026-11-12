module

public import SympyProofs.LinearAlgebra.MatrixTrace.Basic
public import SympyProofs.LinearAlgebra.MatrixTrace.Kronecker
public import SympyProofs.LinearAlgebra.MatrixTrace.KroneckerBlocks
public import SympyProofs.LinearAlgebra.MatrixTrace.MatrixUnit
public import SympyProofs.LinearAlgebra.MatrixTrace.MatrixUnitBounds

/-! Traces and rectangular diagonal sums.

* `Basic` defines `Matrix.diagonalSum`, proves its linearity and transpose identity,
  and relates it to ordinary trace when the dimensions agree.
* `Kronecker` defines row-major Kronecker products and proves the quotient/remainder
  formula for their diagonal sums and traces, allowing rectangular factors. It also
  factors traces across consecutive groups whose total dimensions are square.
* `KroneckerBlocks` decomposes a square Kronecker-product trace into traces of
  square slices and expresses it as the trace of an ordinary product. At most
  `m + n - 1` slices are nonempty for an `m × n` first factor.
* `MatrixUnit` proves the Kronecker-delta trace, entry-extraction, product, and
  rectangular Kronecker-product formulas for matrix units.
* `MatrixUnitBounds` extends matrix units to arbitrary integer indices and proves
  the bounds-sensitive trace formula, an integer-sign representation over any ring,
  and the real-sign formula as a corollary.

The product-of-traces identity is available for square factors. Rectangular
diagonal sums do not in general satisfy that identity.
-/
