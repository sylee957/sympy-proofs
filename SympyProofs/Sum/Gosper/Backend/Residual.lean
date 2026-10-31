module

public import SympyProofs.Sum.Gosper.Backend.Inverse

/-! Compact residual conditions from the right-block pivot rows. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] {m n : ℕ}

/-- Append the transformed values at right-block pivots, without testing their values. -/
def RrefResult.residualEntries {α : Type*} (r : RrefResult K m (n + m))
    (values : Fin m → α) : Array α :=
  (r.pivots.zipIdx.attach.filterMap fun ⟨(pivot, row), hp⟩ =>
    if pivot.val < n then none else
      some (values ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩)).toArray

omit [Field K] in
theorem RrefResult.mem_residualEntries {α : Type*} (r : RrefResult K m (n + m))
    (values : Fin m → α) (value : α) :
    value ∈ r.residualEntries values ↔
      ∃ (i : Fin m) (p : Fin (n + m)),
        r.pivots[i.val]? = some p ∧ n ≤ p.val ∧ values i = value := by
  simp only [residualEntries, List.mem_toArray, List.mem_filterMap,
    List.mem_attach, true_and]
  constructor
  · rintro ⟨⟨⟨p, row⟩, hp⟩, hv⟩
    dsimp at hv
    split_ifs at hv with hleft
    refine ⟨⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩, p,
      List.mk_mem_zipIdx_iff_getElem?.mp hp, Nat.le_of_not_gt hleft, ?_⟩
    exact Option.some.inj hv
  · rintro ⟨i, p, hp, hright, hv⟩
    refine ⟨⟨(p, i.val), List.mk_mem_zipIdx_iff_getElem?.mpr hp⟩, ?_⟩
    simpa [not_lt.mpr hright] using congrArg some hv

omit [Field K] in
/-- Mapping values commutes with retaining the right-pivot residual entries. -/
theorem RrefResult.residualEntries_map {α β : Type*} (r : RrefResult K m (n + m))
    (values : Fin m → α) (f : α → β) :
    (r.residualEntries values).map f = r.residualEntries (f ∘ values) := by
  apply Array.toList_inj.mp
  simp only [residualEntries, Array.toList_map, List.toList_toArray, List.map_filterMap]
  congr 1
  funext p
  rcases p with ⟨⟨pivot, row⟩, hp⟩
  dsimp only
  split_ifs <;> rfl

/-- Missing pivot rows are zero rows, so omitting them preserves the consistency
criterion for a transformed right-hand side. -/
theorem RrefResult.residualEntries_zero_iff
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (rhs : Fin m → K) :
    (∀ value ∈ r.residualEntries (r.rightMatrix.mulVec rhs), value = 0) ↔
      r.leftResidual (r.rightMatrix.mulVec rhs) = 0 := by
  constructor
  · intro h
    ext i
    cases hp : r.pivots[i.val]? with
    | none =>
      simp [leftResidual, hp, rightMatrix, Matrix.mulVec, dotProduct, hr.zero_row i hp]
    | some p =>
      by_cases hleft : p.val < n
      · simp [leftResidual, hp, hleft]
      · have hm : r.rightMatrix.mulVec rhs i ∈
            r.residualEntries (r.rightMatrix.mulVec rhs) := by
          exact (r.mem_residualEntries _ _).mpr
            ⟨i, p, hp, Nat.le_of_not_gt hleft, rfl⟩
        simpa [leftResidual, hp, hleft] using h _ hm
  · intro h value hv
    obtain ⟨i, p, hp, hright, hi⟩ := (r.mem_residualEntries _ _).mp hv
    have hz : r.rightMatrix.mulVec rhs i = 0 := by
      simpa [leftResidual, hp, not_lt.mpr hright] using congrFun h i
    exact hi.symm.trans hz

end Gosper.Algorithm
