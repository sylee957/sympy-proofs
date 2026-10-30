module

public import SympyProofs.Gosper.ShiftlessDecomposition.Primitives
public import SympyProofs.Gosper.ShiftlessDecomposition.Algorithm
public import SympyProofs.Gosper.ShiftlessDecomposition.Basic
public import SympyProofs.Gosper.ShiftlessDecomposition.Reference
public import SympyProofs.Gosper.ShiftlessDecomposition.Correctness
public import SympyProofs.Gosper.ShiftlessDecomposition.Modular

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
The primitive contract supplies gcd, derivative, and complete integer-shift
enumeration without duplicates for monic square-free inputs over `K`.
The decomposition proves these preconditions at every shift call.
Division and remainder use the polynomial
operators. The reference backend uses a resultant; the optional `ModularShifts`
backend over ℚ uses supplied finite-field factorization and Hensel lifting.

`Decomposition.Valid` specifies exact reconstruction, positive multiplicities,
square-free shift-free bases, and separation of different bases at every integer
shift. `decompose_sound` proves this full specification. `decompose_complete`
states successful construction for every nonzero input; `exists_valid_iff`
characterizes nonzero input as the exact existence condition.

`Algorithm` contains the result types, shift enumeration, and the imperative
`decompose`, with inline loops for layer extraction, shift tests,
refinement, multiplicities, and grouping.
Integer shifts, intermediate collections, groups, and occurrences are stored in arrays.
The proof modules retain pure specifications used by the loop invariants.
`Progress` and `Layers` establish the layer loop invariant and prove that its
degree bound suffices. `Support` proves that the first layer contains all factors.
`Refinement` and `Shifts` establish the homogeneous gcd partition and
its translation compatibility. `Multiplicities`, `Classes`, and `Grouping` prove
weighted reconstruction and the required class properties. `Correctness` connects
these proofs to `decompose`. `referencePrimitives_valid` realizes the primitive
contract with Mathlib's noncomputable operations.
`modularPrimitives_valid` supplies the same contract from the modular backend's
arithmetic contracts, and `decompose_modular_sound` proves the resulting rational
decomposition correct end to end.
-/
