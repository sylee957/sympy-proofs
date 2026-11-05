module

public import Mathlib

/-! Imperative Gauss–Jordan elimination over a field. `Vector` is Lean's
size-indexed array: its size proof is erased, and `set` updates the underlying
array in place when uniquely owned. `rref` accepts nested vectors directly;
all entry accesses and writes use these array buffers.

Pivot rows are swapped into consecutive slots. A separate optional pivot index
marks each used row. Both buffers are returned directly, including unused zero
rows. Each pivot row is normalized to have pivot entry one before its column
is eliminated. -/

@[expose] public section

namespace SympyProofs.Rref

/-- The computed rows and their optional pivot columns, including trailing zero rows. -/
structure RrefOutput (F : Type*) (m n : ℕ) where
  rows : Vector (Vector F n) m
  pivots : Vector (Option (Fin n)) m

/-- A constant-time entry-access view of an already materialized buffer. -/
def toMatrix {R : Type*} {m n : ℕ} (A : Vector (Vector R n) m) :
    Matrix (Fin m) (Fin n) R := fun i j => A[i.val][j.val]

variable {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}

/-- Dense monic RREF with consecutive pivot rows and suffix search.
Normalize each pivot row, eliminate its column above and below, and skip rows
whose entry is already zero. Only trailing columns need arithmetic.
The loop includes the identity block when the input is augmented.
Validity is proved separately; no output compaction is needed. -/
def rref (A : Vector (Vector F n) m) : RrefOutput F m n := Id.run do
  let mut rows := A
  let mut pivots : Vector (Option (Fin n)) m := Vector.replicate m none
  let mut rank : ℕ := 0
  for c in List.finRange n do
    if h : rank < m then
      let p : Fin m := ⟨rank, h⟩
      let mut selected : Option (Fin m) := none
      let mut a : F := 0
      for hi : i in [rank:m] do
        if rows[i][c.val] == 0 then continue
        selected := some ⟨i, hi.upper⟩
        a := rows[i][c.val]
        break
      let some r := selected | continue
      rows := rows.swap p.val r.val
      let mut pivot := rows[p.val]
      let scale := a⁻¹
      for hj : j in [c.val + 1:n] do
        pivot := pivot.set j (pivot[j] * scale)
      pivot := pivot.set c.val 1
      rows := rows.set p.val pivot
      for i in List.finRange m do
        if i == p then continue
        let b := rows[i.val][c.val]
        if b == 0 then continue
        let mut row := rows[i.val]
        for hj : j in [c.val + 1:n] do
          row := row.set j (row[j] - b * pivot[j])
        row := row.set c.val 0
        rows := rows.set i.val row
      pivots := pivots.set p.val (some c)
      rank := rank + 1
    else
      break
  return { rows := rows, pivots := pivots }

end SympyProofs.Rref
