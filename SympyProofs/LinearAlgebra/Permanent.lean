module

public import SympyProofs.LinearAlgebra.Permanent.Adjugate
public import SympyProofs.LinearAlgebra.Permanent.Block
public import SympyProofs.LinearAlgebra.Permanent.Mul
public import SympyProofs.LinearAlgebra.Permanent.Ryser

/-! Permanents, permanental minors, and permanental adjugates over commutative semirings.

* `Basic` imports Mathlib's transpose, permutation, and scaling identities, and proves
  row/column additivity and the rank-one formula.
* `Minor` defines `Matrix.permanentalMinor` using bijections of the remaining indices and proves
  its reindexing and basis-column replacement formulas.
* `Adjugate` proves row/column expansions, adjugate product entries, and trace identities.
* `Block` proves the triangular and block triangular product formulas.
* `Mul` expands matrix products, identifying the repeated-column terms that prevent
  multiplicativity.
* `Ryser` proves the inclusion-exclusion formula over a commutative ring.

Scalar differentiation is developed separately in `MatrixDerivative.Permanent`.
-/
