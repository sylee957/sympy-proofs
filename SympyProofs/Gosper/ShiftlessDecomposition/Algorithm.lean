module

public import SympyProofs.Gosper.ShiftlessDecomposition.Primitives

/-!
# Total shiftless decomposition

This module defines the result types `Occurrence`, `Group`, and `Decomposition`,
the resultant-based shift enumeration, and the imperative decomposition algorithm.

`decompose ops D` returns a `Decomposition K` directly. The definition takes no
proof arguments; the primitive contracts and nonzero-input assumption appear
only in its correctness theorems. Zero input produces coefficient zero and no
groups.

The construction extracts square-free layers, takes the first layer as their support,
and splits that support by every shifted layer. Successive gcd partitions replace
the previous overlap-search loop. A block's exponent is the number of layers it
divides. Each translation class is represented by its least integer shift.

For characteristic-zero fields, `decompose_sound` in `Correctness` proves the full
output specification. The construction uses inline loops in `decompose`. The supporting
modules provide pure specifications and prove the degree bound, factor reconstruction,
uniform multiplicities, and translation-class compatibility without assuming any
of these as primitives.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

structure Occurrence where
  shift : ℤ
  multiplicity : ℕ
  deriving DecidableEq

structure Group (K : Type*) [Semiring K] where
  base : Polynomial K
  occurrences : Array Occurrence

structure Decomposition (K : Type*) [Semiring K] where
  coefficient : K
  groups : Array (Group K)

/-- Enumerate integer shifts with a common factor.
The inner variable is the shift; the resultant eliminates the outer one.
Remove repeated factors from the resultant before finding its integer roots. -/
def shifts (ops : Primitives K) (p q : Polynomial K) : Array ℤ := Id.run do
  let p := p.map (Polynomial.C : K →+* Polynomial K)
  let q := q.map (Polynomial.C : K →+* Polynomial K)
  let q := taylor (X : Polynomial K) q
  let r := ops.resultant p q
  let r := r / ops.gcd r (ops.derivative r)
  return ops.integerRoots r

/-- Construct a shiftless decomposition. Correctness assumes characteristic zero,
`ops.Valid`, and nonzero input; these conditions appear only in the theorems. -/
def decompose (ops : Primitives K) (D : Polynomial K) : Decomposition K := Id.run do
  if D.natDegree = 0 then return { coefficient := D.leadingCoeff, groups := #[] }
  let mut remaining := C D.leadingCoeff⁻¹ * D
  let S := remaining / ops.gcd remaining (ops.derivative remaining)
  let mut layers := #[S]
  remaining := remaining / S
  for _ in [1:D.natDegree] do
    if remaining = 1 then break
    let layer := remaining / ops.gcd remaining (ops.derivative remaining)
    layers := layers.push layer
    remaining := remaining / layer
  let mut tests := #[]
  for h in shifts ops S S do
    for a in layers do
      tests := tests.push (taylor (h : K) a)
  let mut blocks := #[S]
  for test in tests do
    let mut next := #[]
    for b in blocks do
      let g := ops.gcd b test
      let q := b / g
      if g ≠ 1 then next := next.push g
      if q ≠ 1 then next := next.push q
    blocks := next
  let mut groups : Array (Group K) := #[]
  for b in blocks do
    let shifts := shifts ops S b
    if ∀ h ∈ shifts, 0 ≤ h then
      -- Record the unshifted base first.
      let mut baseMultiplicity : ULift ℕ := 0
      for a in layers do
        if a % b = 0 then baseMultiplicity := baseMultiplicity + 1
      let mut occurrences : ULift (Array Occurrence) :=
        { down := #[{ shift := 0, multiplicity := baseMultiplicity.down }] }
      for h in (shifts.filter (· != 0)).mergeSort (· ≤ ·) do
        let shifted := taylor (h : K) b
        -- Lift the counter to the universe of the surrounding Id computation.
        let mut multiplicity : ULift ℕ := 0
        for a in layers do
          if a % shifted = 0 then multiplicity := multiplicity + 1
        occurrences :=
          { down := occurrences.down.push { shift := h, multiplicity := multiplicity.down } }
      groups := groups.push { base := b, occurrences := occurrences.down }
  return { coefficient := D.leadingCoeff, groups := groups }

end Gosper.ShiftlessDecomposition
