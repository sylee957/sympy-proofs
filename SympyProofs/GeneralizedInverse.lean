module

public import SympyProofs.GeneralizedInverse.Correctness

/-! Canonical generalized inverses from augmented RREF.

The independent RREF theory and algorithm live in `SympyProofs.Rref`.
This directory defines augmentation, inverse extraction, and the additional
support conditions that characterize the resulting generalized inverse.

* `Matrix.IsReflexiveGeneralizedInverse A G`, defined in `GeneralizedInverse.Basic`,
  states the two generalized-inverse identities for arbitrary finite matrix indices
  over a semiring, independently of RREF.
* `Matrix.existsUnique_canonicalGeneralizedInverse` specifies membership in the
  range and kernel using universally quantified equivalences. A vector belongs
  precisely when it vanishes at the last nonzero coordinates of vectors in the
  input's kernel or range, respectively. `IsGreatest (Function.support x) j`
  means that `j` is the last nonzero coordinate of `x`. Exactly one reflexive
  generalized inverse satisfies these conditions.
* `RrefResult.inverse F` directly extracts the canonical generalized inverse from
  a certificate for `[A | I]`, without sorting the stored rows.
* `RrefResult.inverse_reflexive` proves `A * G * A = A` and `G * A * G = G` in `F`.
* `RrefResult.existsUnique_canonicalInverse` and `RrefResult.inverse_eq` prove
  uniqueness with the prescribed coordinate range and kernel, independently of
  storage order, row scales, or the valid RREF implementation.
* `generalizedInverse A` takes `Vector (Vector F n) m` over a field `F` and returns
  `Vector (Vector F m) n`. It builds the augmented vector input to `rref`, then
  copies the coefficient-pivot rows of the right block into the inverse buffer
  with nested loops. Unit pivots make further normalization unnecessary.
  `generalizedInverse_reflexive` and `generalizedInverse_unique` use `toMatrix`
  views of the buffers to prove the generalized-inverse identities and the
  canonical characterization.
  `generalizedInverse_range_eq` and `generalizedInverse_ker_eq` identify the output's
  range and kernel with the independently specified subspaces.
  `generalizedInverse_unique_of_range_eq_of_ker_eq` proves uniqueness among
  reflexive inverses with the computed range and kernel;
  `generalizedInverse_algorithm_unique` lifts this to equality of implementations
  as vector-valued functions.

For example, `generalizedInverse` sends `[2]` over `ℚ` to `[1/2]` over `ℚ`.
The abstract `RrefResult` theory also supports unnormalized certificates over an
integral domain, interpreted in its fraction field. The executable `rref` and
`generalizedInverse` operate directly over a field.
-/
