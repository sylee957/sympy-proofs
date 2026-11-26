module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.ParameterStep

/-! The final rows identify the original coordinates with combinations of the solution columns. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n w : ℕ}

/-- A unit row and the negated column entries identify one original parameter
with the corresponding coordinate of a linear combination. -/
theorem parameterRow {A : Type} (cols : List A) (params : A → List (K R 0))
    (p : Fin w → k) (q : Fin cols.length → k)
    (i : Fin w) :
    Model.rowHolds k (Linear.unit (F := K R 0) w i.val ++
        cols.map (fun v => -(params v).getD i.val 0))
      (List.ofFn p ++ List.ofFn q) ↔
    (Linear.accumulate cols (fun v => Linear.vector (Model.constantHom k) w (params v)) q) i =
      p i := by
  classical
  rw [← List.ofFn_fin_append, functional_ofFn, Linear.functional_apply, Fin.sum_univ_add]
  have left (j : Fin w) :
      (Linear.unit (F := K R 0) w i.val ++
        cols.map (fun v => -(params v).getD i.val 0)).getD
        (Fin.castAdd cols.length j) 0 = (if j = i then 1 else 0 : K R 0) := by
    simp [Linear.unit, List.getD_eq_getElem?_getD, List.getElem?_append, j.isLt, Fin.ext_iff]
  have right (j : Fin cols.length) :
      (Linear.unit (F := K R 0) w i.val ++
        cols.map (fun v => -(params v).getD i.val 0)).getD
        (Fin.natAdd w j) 0 = -(params (cols.get j)).getD i.val 0 := by
    simp [Linear.unit, List.getD_eq_getElem?_getD, List.get_eq_getElem]
  simp only [left, right, Fin.append_left, Fin.append_right,
    apply_ite (Model.constantHom k), map_one, map_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_neg, neg_mul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero]
  rw [Linear.accumulate_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Linear.vector]
  simp [mul_comm, eq_comm]

private theorem row_value (cols : List (Column R n)) (p : Fin w → k) (q : Fin cols.length → k)
    (i : Fin w) :
    Model.rowHolds k (Linear.unit (F := K R 0) w i.val ++
        cols.map (fun v : Column R n => -v.params.getD i.val 0))
      (List.ofFn p ++ List.ofFn q) ↔
    (Linear.accumulate cols (Column.value k w) q).1 i = p i := by
  simpa only [Linear.accumulate_apply, Prod.fst_sum, Prod.smul_fst, Column.value] using
    parameterRow k cols Column.params p q i

/-- The coordinates, field generators and rows returned by the solver describe precisely
the linear combinations of the computed columns. -/
theorem describe_spec (width : ℕ) (den : Poly (K R n)) (cols : List (Column R n))
    (p : Fin width → k) (y : M k (n + 1)) :
    (∃ d : List k, d.length = (describe width den cols).1.length ∧
      y = Model.linearCombination k d (describe width den cols).1 ∧
      ∀ row ∈ (describe width den cols).2, Model.rowHolds k row (List.ofFn p ++ d)) ↔
    ∃ q : Fin cols.length → k, (Linear.accumulate cols (Column.value k width) q).1 = p ∧
      y = Model.linearCombination k (List.ofFn q) (cols.map fun v => K.join v.solution den) := by
  simp only [describe, List.length_map, List.forall_mem_map]
  constructor
  · rintro ⟨ds,hd,hy,hr⟩
    let q (i : Fin cols.length) := ds.get (Fin.cast hd.symm i)
    have hq : List.ofFn q = ds := by
      apply List.ext_getElem
      · simpa using hd.symm
      · intro i hi hj
        simp [q]
    refine ⟨q,funext fun i => (row_value k cols p q i).mp ?_,by rwa [hq]⟩
    rw [hq]
    exact hr i (List.mem_range.mpr i.isLt)
  · rintro ⟨q,hp,hy⟩
    refine ⟨List.ofFn q,List.length_ofFn,hy,?_⟩
    intro i hi
    let j : Fin width := ⟨i, List.mem_range.mp hi⟩
    exact (row_value k cols p q j).mpr (congrFun hp j)

end SympyProofs.Calculus.Antiderivative.Solve
