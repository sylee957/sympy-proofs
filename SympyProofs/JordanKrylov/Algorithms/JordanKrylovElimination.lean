import SympyProofs.JordanKrylov.Algorithms.Operations

/-! # Simultaneous column elimination

Columns are stored as pairs instead of allocating the stacked `2n × k` matrix.
Pivots are chosen only from the upper half; every operation acts on both halves.
-/
namespace SympyProofs.JordanKrylov

/-- A column of the paper's stacked matrix `[D'; D]`. -/
structure PairedColumn (K : Type*) (n : ℕ) where
  top : Fin n → K
  bottom : Fin n → K

/-- Reduce a candidate against stored pivot columns, carrying the same
operations through its lower half. Stored pivots must have nonzero entries. -/
def reducePairedColumn {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    PairedColumn K n := Id.run do
  let mut r := v
  for (i, w) in D do
    let c := r.top i / w.top i
    r := { top := r.top - c • w.top, bottom := r.bottom - c • w.bottom }
  return r

/-- Insert a column into the echelon basis of the upper halves.
A zero upper remainder is discarded. -/
def insertPairedColumn {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    Array (Fin n × PairedColumn K n) := Id.run do
  let r := reducePairedColumn D v
  for i in List.finRange n do
    if r.top i ≠ 0 then
      return D.push (i, r)
  return D

end SympyProofs.JordanKrylov
