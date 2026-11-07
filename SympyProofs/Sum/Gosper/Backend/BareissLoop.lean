module

public import SympyProofs.Sum.Gosper.Backend.Bareiss

/-! The imperative Bareiss loop and its recursive proof model. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L] [Div K] [Div L]
variable {m n : ℕ} [DecidableEq K]

omit [DecidableEq K] in
theorem bareiss_rows_rhs_foldl (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (p previous : K) (row : Vector K n) (rhs : L) :
    (List.finRange m).foldl (fun current i =>
      (current.1.set i.val (Vector.ofFn fun j : Fin n =>
        (p * current.1[i.val][j.val] - current.1[i.val][c.val] * row[j.val]) / previous),
        current.2.set i.val ((algebraMap K L p * current.2[i.val] -
          algebraMap K L (current.1[i.val][c.val]) * rhs) / algebraMap K L previous)))
        (A, b) =
      (A.map (fun source => Vector.ofFn fun j : Fin n =>
        (p * source[j.val] - source[c.val] * row[j.val]) / previous),
        Vector.ofFn (fun i : Fin m => (algebraMap K L p * b[i.val] -
          algebraMap K L (A[i.val][c.val]) * rhs) / algebraMap K L previous)) := by
  refine (elimination_joint_foldl
    (fun (source : Vector K n) (value : L) =>
      (Vector.ofFn (fun j : Fin n =>
        (p * source[j.val] - source[c.val] * row[j.val]) / previous),
        (algebraMap K L p * value - algebraMap K L source[c.val] * rhs) /
          algebraMap K L previous)) A b).trans ?_
  apply Prod.ext
  · ext i hi
    simp
  · rfl

/-- Proof-only forward phase; `gosperSolve` contains this loop inline. -/
def bareissForwardRun (columns : List (Fin n)) (A : Vector (Vector K n) m)
    (b : Vector L m) (steps : List (EliminationStep K L n)) (previous : K) :
    Vector (Vector K n) m × Vector L m × List (EliminationStep K L n) × K := Id.run do
  let mut A := A
  let mut b := b
  let mut steps := steps
  let mut previous := previous
  for c in columns do
    let pivot : Option (Fin m) := Id.run do
      let mut pivot : Option (Fin m) := none
      for r in List.finRange m do
        if A[r.val][c.val] ≠ 0 then
          pivot := some r
          break
      return pivot
    if let some r := pivot then
      let row := A[r.val]
      let p := row[c.val]
      let rhs := b[r.val]
      steps := (c, p, row, rhs) :: steps
      for i in List.finRange m do
        let source := A[i.val]
        let a := source[c.val]
        b := b.set i.val ((algebraMap K L p * b[i.val] - algebraMap K L a * rhs) /
          algebraMap K L previous)
        let updated := Id.run do
          let mut updated := source
          for j in List.finRange n do
            updated := updated.set j.val ((p * source[j.val] - a * row[j.val]) / previous)
          return updated
        A := A.set i.val updated
      previous := p
  return (A, b, steps, previous)

theorem bareissForwardRun_eq (columns : List (Fin n)) (A : Vector (Vector K n) m)
    (b : Vector L m) (steps : List (EliminationStep K L n)) (previous : K) :
    bareissForwardRun columns A b steps previous =
      columns.foldl bareissForwardStep (A, b, steps, previous) := by
  have hrun (v : Vector K n) : (pure v : Id (Vector K n)).run = v := rfl
  simp only [bareissForwardRun, bind_pure, elimination_fill_eq, pure_bind,
    List.forIn_pure_yield_eq_foldl, hrun, bareiss_rows_rhs_foldl]
  change (forIn (m := Id) columns (A, b, steps, previous) _) = _
  trans (forIn columns (A, b, steps, previous) (fun c state =>
    pure (ForInStep.yield (bareissForwardStep state c))) : Id _)
  · congr 1
    funext c state
    rw [elimination_pivotLoop_eq]
    simp only [bareissForwardStep]
    split_ifs
    · simp [Id.run, bareissRows, bareissRhs, eliminationRows, eliminationRhs,
        Vector.map_map, Function.comp_def]
    · rfl
  · exact List.forIn_pure_yield_eq_foldl _ _

end Gosper.Algorithm
