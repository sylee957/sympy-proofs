module

public import SympyProofs.Gosper.Algorithm.Polynomial

/-! Column elimination with an explicit, verified reconstruction step. -/

@[expose] public section

namespace Gosper.Algorithm.Linear

variable {K : Type*} [Field K] [DecidableEq K] {m n : ℕ}

def tailMatrix (A : Matrix (Fin m) (Fin (n + 1)) K) : Matrix (Fin m) (Fin n) K :=
  fun i j => A i j.succ

def reduceMatrix (A : Matrix (Fin m) (Fin (n + 1)) K) (i : Fin m) :
    Matrix (Fin m) (Fin n) K :=
  fun j k => A j k.succ - (A j 0 / A i 0) * A i k.succ

def reduceRhs (A : Matrix (Fin m) (Fin (n + 1)) K) (b : Fin m → K) (i : Fin m) :
    Fin m → K := fun j => b j - (A j 0 / A i 0) * b i

def recover (A : Matrix (Fin m) (Fin (n + 1)) K) (b : Fin m → K) (i : Fin m)
    (y : Fin n → K) : Fin (n + 1) → K :=
  Fin.cons ((b i - (tailMatrix A).mulVec y i) / A i 0) y

omit [DecidableEq K] in
theorem mulVec_expand (A : Matrix (Fin m) (Fin (n + 1)) K) (x : Fin (n + 1) → K)
    (j : Fin m) :
    A.mulVec x j = A j 0 * x 0 + (tailMatrix A).mulVec (fun k => x k.succ) j := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailMatrix]

omit [DecidableEq K] in
theorem reduceMatrix_mulVec (A : Matrix (Fin m) (Fin (n + 1)) K) (i j : Fin m)
    (y : Fin n → K) :
    (reduceMatrix A i).mulVec y j = (tailMatrix A).mulVec y j -
      (A j 0 / A i 0) * (tailMatrix A).mulVec y i := by
  simp only [Matrix.mulVec, dotProduct, reduceMatrix, tailMatrix, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

omit [DecidableEq K] in
theorem recover_correct (A : Matrix (Fin m) (Fin (n + 1)) K) (b : Fin m → K)
    (i : Fin m) (hp : A i 0 ≠ 0) (y : Fin n → K) :
    (reduceMatrix A i).mulVec y = reduceRhs A b i ↔ A.mulVec (recover A b i y) = b := by
  simp only [funext_iff, mulVec_expand, recover, Fin.cons_zero, Fin.cons_succ,
    reduceMatrix_mulVec, reduceRhs]
  apply forall_congr'
  intro j
  constructor <;> intro h <;> field_simp at h ⊢ <;> linear_combination h

omit [DecidableEq K] in
theorem project_solution (A : Matrix (Fin m) (Fin (n + 1)) K) (b : Fin m → K)
    (i : Fin m) (hp : A i 0 ≠ 0) (x : Fin (n + 1) → K) (hx : A.mulVec x = b) :
    (reduceMatrix A i).mulVec (fun k => x k.succ) = reduceRhs A b i := by
  have h0 := congrFun hx i
  rw [mulVec_expand] at h0
  have he : recover A b i (fun k => x k.succ) = x := by
    ext k
    refine Fin.cases ?_ (fun j => rfl) k
    simp only [recover, Fin.cons_zero]
    field_simp
    linear_combination -h0
  exact (recover_correct A b i hp _).mpr (he.symm ▸ hx)

/-- Eliminate the first column, recurse on the remaining columns, then recover
the pivot variable. A zero column gives a free variable, set to zero. -/
def eliminate : (n : ℕ) → Matrix (Fin m) (Fin n) K → (Fin m → K) → Option (Fin n → K)
  | 0, _, b => if b = 0 then some 0 else none
  | n + 1, A, b =>
    match (List.finRange m).find? (fun i => A i 0 != 0) with
    | none => (eliminate n (tailMatrix A) b).map (Fin.cons 0)
    | some i => (eliminate n (reduceMatrix A i) (reduceRhs A b i)).map (recover A b i)

/-- Both return branches are correct; in particular `none` proves inconsistency. -/
theorem eliminate_spec (n : ℕ) (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    match eliminate n A b with
    | some x => A.mulVec x = b
    | none => ¬∃ x, A.mulVec x = b := by
  induction n generalizing b with
  | zero =>
    by_cases hb : b = 0
    · simp [eliminate, hb]
    · simp [eliminate, hb, eq_comm]
  | succ n ih =>
    cases hp : (List.finRange m).find? (fun i => A i 0 != 0) with
    | none =>
      have hz : ∀ i, A i 0 = 0 := by
        intro i
        have hi := List.find?_eq_none.mp hp i (List.mem_finRange i)
        simpa using hi
      have ih' := ih (tailMatrix A) b
      cases he : eliminate n (tailMatrix A) b with
      | none =>
        simp only [eliminate, hp, he, Option.map_none]
        simp only [he] at ih'
        rintro ⟨x, hx⟩
        apply ih'
        refine ⟨fun k => x k.succ, ?_⟩
        ext i
        simpa [mulVec_expand, hz i] using congrFun hx i
      | some y =>
        simp only [eliminate, hp, he, Option.map_some]
        simp only [he] at ih'
        ext i
        simpa [mulVec_expand, hz i] using congrFun ih' i
    | some i =>
      have hi : A i 0 ≠ 0 := by simpa using List.find?_some hp
      have ih' := ih (reduceMatrix A i) (reduceRhs A b i)
      cases he : eliminate n (reduceMatrix A i) (reduceRhs A b i) with
      | none =>
        simp only [eliminate, hp, he, Option.map_none]
        simp only [he] at ih'
        rintro ⟨x, hx⟩
        exact ih' ⟨_, project_solution A b i hi x hx⟩
      | some y =>
        simp only [eliminate, hp, he, Option.map_some]
        simp only [he] at ih'
        exact (recover_correct A b i hi y).mp ih'

theorem eliminate_some (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (x : Fin n → K) (h : eliminate n A b = some x) : A.mulVec x = b := by
  simpa [h] using eliminate_spec n A b

theorem eliminate_none_iff (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    eliminate n A b = none ↔ ¬∃ x, A.mulVec x = b := by
  cases h : eliminate n A b with
  | none => simpa [h] using eliminate_spec n A b
  | some x =>
    simp only [Option.some_ne_none, false_iff, not_not]
    exact ⟨x, eliminate_some A b x h⟩

end Gosper.Algorithm.Linear
