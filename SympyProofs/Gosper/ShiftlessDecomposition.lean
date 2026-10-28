module

public import SympyProofs.Gosper.ShiftlessDecomposition.Primitives
public import SympyProofs.Gosper.ShiftlessDecomposition.Algorithm
public import SympyProofs.Gosper.ShiftlessDecomposition.Basic
public import SympyProofs.Gosper.ShiftlessDecomposition.Reference
public import SympyProofs.Gosper.ShiftlessDecomposition.Correctness

/-!
# Shiftless decomposition over characteristic-zero fields

The coefficient field `K` can be any characteristic-zero field with decidable
equality, including number fields and rational-function fields such as `ℚ(t)`.
Shifts are still integers, cast into `K`.

`ShiftlessDecomposition.decompose ops D` builds a decomposition directly
from square-free layers, gcd refinement by shifted layers, and translation
grouping. It returns a `Decomposition` without proof arguments, failure branches,
or a final validity check. The assumptions `hops : ops.Valid` and `hD : D ≠ 0`
appear only in the correctness theorems. Zero input returns coefficient zero
and an empty array of groups.
The primitive contract supplies gcd, derivative, resultant, and complete
integer-root enumeration without duplicates over `K`. Division and remainder use
the polynomial operators. No irreducible factorization is assumed.

`Decomposition.Valid` specifies exact reconstruction, positive multiplicities,
square-free shift-free bases, and separation of different bases at every integer
shift. `decompose_sound` proves this full specification. `decompose_complete`
states successful construction for every nonzero input; `exists_valid_iff`
characterizes nonzero input as the exact existence condition.

`Algorithm` contains the result types, shift enumeration, and the imperative
`decompose`, with inline loops for layer extraction, shift tests,
refinement, multiplicities, and grouping.
Integer roots, intermediate collections, groups, and occurrences are stored in arrays.
The proof modules retain pure specifications used by the loop invariants.
`Progress` and `Layers` establish the layer loop invariant and prove that its
degree bound suffices. `Support` proves that the first layer contains all factors.
`Refinement` and `Shifts` establish the homogeneous gcd partition and
its translation compatibility. `Multiplicities`, `Classes`, and `Grouping` prove
weighted reconstruction and the required class properties. `Correctness` connects
these proofs to `decompose`. `referencePrimitives_valid` realizes the primitive
contract with Mathlib's noncomputable operations.
-/
