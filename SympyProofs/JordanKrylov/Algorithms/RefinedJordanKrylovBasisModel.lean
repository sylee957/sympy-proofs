import SympyProofs.JordanKrylov.Algorithms.RefinedJordanKrylovBasis
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisLemmas

namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- The last state update is unnecessary when only the accumulated table is returned. -/
theorem fold_krylov_skip_last {α β : Type} (insert : α → β → α) (next : β → β)
    (d : ℕ) (s : α × β) :
    ((List.range d).foldl (fun s j =>
      (insert s.1 s.2, if j + 1 < d then next s.2 else s.2)) s).1 =
    ((List.range d).foldl (fun s _ => (insert s.1 s.2, next s.2)) s).1 := by
  cases d with
  | zero => rfl
  | succ k =>
    have hp (xs : List ℕ) (h : ∀ j ∈ xs, j < k) (s : α × β) :
        xs.foldl (fun s j =>
          (insert s.1 s.2, if j + 1 < k + 1 then next s.2 else s.2)) s =
        xs.foldl (fun s _ => (insert s.1 s.2, next s.2)) s := by
      induction xs generalizing s with
      | nil => rfl
      | cons j xs ih =>
        simp only [List.foldl_cons, show j + 1 < k + 1 from Nat.succ_lt_succ (h j (by simp)), ite_true]
        exact ih (fun j hj => h j (by simp [hj])) _
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hp (List.range k) (fun j hj => List.mem_range.mp hj)]

theorem paired_krylov_skip_last {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (d : ℕ)
    (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) :
    ((List.range d).foldl (fun s j =>
      (insertPairedColumn s.1 s.2, if j + 1 < d then
        { top := A *ᵥ s.2.top, bottom := A *ᵥ s.2.bottom } else s.2)) s).1 =
    ((List.range d).foldl (fun s _ =>
      (insertPairedColumn s.1 s.2, { top := A *ᵥ s.2.top, bottom := A *ᵥ s.2.bottom })) s).1 :=
  fold_krylov_skip_last insertPairedColumn
    (fun w => { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }) d s

/-- Optional preprocessing before entering a lower layer. -/
def refinedPreprocess (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (preprocess : Bool) (limit ℓ : ℕ) (pending : ℕ → List (Fin n → K)) :=
  if preprocess ∧ ℓ < limit ∧ pending ℓ ≠ [] then
    reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) pending ℓ
  else pending

/-- Recursive proof model for the imperative descending loops. -/
def refinedElimination (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit : ℕ)
    (ℓ : ℕ) (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (basis : Finset (Fin n → K)) (used : ℕ)
    (D : Array (Fin n × PairedColumn K n)) : Finset (Fin n → K) := Id.run do
  match ℓ, todo with
  | 0, _ => return basis
  | k + 1, [] =>
    if k = 0 then return basis
    let D := D.map (fun (i, w) => (i, { top := w.top, bottom := PolynomialOperations.applyMatrix f A w.bottom }))
    let pending := refinedPreprocess K A f preprocess limit k pending
    return refinedElimination K A f m preprocess limit k (pending k) (Function.update pending k []) basis used D
  | k + 1, v :: rest =>
    let F := PolynomialOperations.applyMatrix f A
    let mut top := v
    for _ in List.range k do
      top := F top
    let r := reducePairedColumn D { top := top, bottom := v }
    if r.top ≠ 0 then
      let basis := insert r.bottom basis
      let used := used + (k + 1)
      if used = m then return basis
      let mut D := D
      let mut w := r
      for _ in List.range f.natDegree do
        D := insertPairedColumn D w
        w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
      return refinedElimination K A f m preprocess limit (k + 1) rest pending basis used D
    else if r.bottom ≠ 0 ∧ 1 < k + 1 then
      let rank := boundedVectorRank F r.bottom k
      let pending := Function.update pending rank (pending rank ++ [r.bottom])
      return refinedElimination K A f m preprocess limit (k + 1) rest pending basis used D
    else
      return refinedElimination K A f m preprocess limit (k + 1) rest pending basis used D
termination_by (ℓ, todo.length)

 theorem refinedElimination_cons
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit k : ℕ)
    (v : Fin n → K) (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (B : Finset (Fin n → K)) (used : ℕ) (D : Array (Fin n × PairedColumn K n)) :
    refinedElimination K A f m preprocess limit (k+1) (v :: todo) pending B used D =
      let r := reducePairedColumn D ⟨(PolynomialOperations.applyMatrix f A)^[k] v, v⟩
      if r.top ≠ 0 then
        if used + (k+1) = m then insert r.bottom B else
          refinedElimination K A f m preprocess limit (k+1) todo pending (insert r.bottom B) (used+(k+1))
            ((List.range f.natDegree).foldl
              (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
                (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩)) (D,r)).1
      else if r.bottom ≠ 0 ∧ 1 < k+1 then
        let rank := boundedVectorRank (PolynomialOperations.applyMatrix f A) r.bottom k
        refinedElimination K A f m preprocess limit (k+1) todo
          (Function.update pending rank (pending rank ++ [r.bottom])) B used D
      else refinedElimination K A f m preprocess limit (k+1) todo pending B used D := by
  rw [refinedElimination]
  have ht := iterate_loop_eq (PolynomialOperations.applyMatrix f A) v k
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind] at ht ⊢
  dsimp only [Bind.bind, Pure.pure] at ht ⊢
  rw [ht]


/-- State generated by Lean's imperative loops, including an early return. -/
abbrev RefinedLoopState (K : Type) (n : ℕ) :=
  Option (Finset (Fin n → K)) × (ℕ → List (Fin n → K)) ×
    Finset (Fin n → K) × ℕ × Array (Fin n × PairedColumn K n)

/-- Proof model of one candidate iteration. -/
def refinedCandidateStep (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m k : ℕ) :
    (Fin n → K) → RefinedLoopState K n → Id (ForInStep (RefinedLoopState K n)) := fun v s =>
  let pending := s.2.1
  let B := s.2.2.1
  let used := s.2.2.2.1
  let D := s.2.2.2.2
  let r := reducePairedColumn D ⟨(PolynomialOperations.applyMatrix f A)^[k] v, v⟩
  if r.top ≠ 0 then
    let B := insert r.bottom B
    let used := used + (k+1)
    if used = m then .done (some B, pending, B, used, D) else
      let D := ((List.range f.natDegree).foldl
        (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
          (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩)) (D,r)).1
      .yield (none, pending, B, used, D)
  else if r.bottom ≠ 0 ∧ 1 < k+1 then
    let rank := boundedVectorRank (PolynomialOperations.applyMatrix f A) r.bottom k
    .yield (none, Function.update pending rank (pending rank ++ [r.bottom]), B, used, D)
  else .yield (none, pending, B, used, D)

/-- Proof model of the outer loop body. -/
def refinedLayerStep (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit : ℕ) : ℕ → RefinedLoopState K n → Id (ForInStep (RefinedLoopState K n)) := fun k s =>
  let pending := refinedPreprocess K A f preprocess limit (k+1) s.2.1
  let out := forIn (m := Id) (pending (k+1))
    (none, Function.update pending (k+1) [], s.2.2.1, s.2.2.2.1, s.2.2.2.2)
    (refinedCandidateStep K A f m k)
  match out.1 with
  | some B => .done (some B, out.2)
  | none =>
    if 1 < k+1 then .yield (none, out.2.1, out.2.2.1, out.2.2.2.1,
      out.2.2.2.2.map (fun (i,w) => (i, ⟨w.top, PolynomialOperations.applyMatrix f A w.bottom⟩)))
    else .yield (none, out.2.1, out.2.2.1, out.2.2.2.1, out.2.2.2.2)

/-- Interpret a completed inner loop using the recursive proof model. -/
def resumeRefined (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit k : ℕ)
    (s : RefinedLoopState K n) : Finset (Fin n → K) :=
  match s.1 with
  | some B => B
  | none => refinedElimination K A f m preprocess limit (k+1) [] s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2

theorem refined_inner_eq_model
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit k : ℕ)
    (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (B : Finset (Fin n → K)) (used : ℕ) (D : Array (Fin n × PairedColumn K n)) :
    resumeRefined K A f m preprocess limit k
      (forIn (m := Id) todo (none, pending, B, used, D) (refinedCandidateStep K A f m k) :
        Id (RefinedLoopState K n)) =
        refinedElimination K A f m preprocess limit (k+1) todo pending B used D := by
  induction todo generalizing pending B used D with
  | nil => rfl
  | cons v todo ih =>
    rw [List.forIn_cons, refinedElimination_cons]
    dsimp only [refinedCandidateStep, Bind.bind, Pure.pure]
    let r := reducePairedColumn D ⟨(PolynomialOperations.applyMatrix f A)^[k] v, v⟩
    by_cases ht : r.top ≠ 0
    · by_cases hs : used + (k+1) = m
      · rw [ite_eq_left ht, ite_eq_left hs, ite_eq_left ht, ite_eq_left hs]
        rfl
      · rw [ite_eq_left ht, ite_eq_right hs, ite_eq_left ht, ite_eq_right hs]
        exact ih _ _ _ _
    · by_cases hb : r.bottom ≠ 0 ∧ 1 < k+1
      · rw [ite_eq_right ht, ite_eq_left hb, ite_eq_right ht, ite_eq_left hb]
        exact ih _ _ _ _
      · rw [ite_eq_right ht, ite_eq_right hb, ite_eq_right ht, ite_eq_right hb]
        exact ih _ _ _ _

/-- Read the returned basis from the loop state. -/
def refinedLoopResult {K : Type} {n : ℕ} (s : RefinedLoopState K n) : Finset (Fin n → K) :=
  s.1.getD s.2.2.1

theorem refined_outer_eq_model
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ) (preprocess : Bool) (limit ℓ : ℕ)
    (pending : ℕ → List (Fin n → K))
    (B : Finset (Fin n → K)) (used : ℕ) (D : Array (Fin n × PairedColumn K n)) :
    refinedLoopResult (forIn (m := Id) (List.range ℓ).reverse (none, pending, B, used, D)
      (refinedLayerStep K A f m preprocess limit) : Id (RefinedLoopState K n)) =
        let pending := refinedPreprocess K A f preprocess limit ℓ pending
        refinedElimination K A f m preprocess limit ℓ (pending ℓ) (Function.update pending ℓ []) B used D := by
  induction ℓ generalizing pending B used D with
  | zero => simp [refinedLoopResult, refinedElimination, Pure.pure, Id.run]
  | succ k ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, List.forIn_cons]
    rw [← refined_inner_eq_model]
    dsimp only [Bind.bind, Pure.pure]
    simp only [refinedLayerStep]
    generalize ho : (forIn (m := Id) ((refinedPreprocess K A f preprocess limit (k+1) pending) (k+1))
      (none, Function.update (refinedPreprocess K A f preprocess limit (k+1) pending) (k+1) [], B, used, D)
      (refinedCandidateStep K A f m k) : Id (RefinedLoopState K n)) = out
    rcases out with ⟨result, V, C, u, E⟩
    cases result with
    | some R => rfl
    | none =>
      dsimp only [resumeRefined]
      by_cases hk : k = 0
      · subst k
        simp [refinedElimination, refinedLoopResult, Pure.pure, Id.run]
      · simp only [show 1 < k+1 by omega, ite_true]
        rw [ih]
        rw [refinedElimination]
        simp only [hk, ite_false, Id.run, Pure.pure]

theorem refined_forIn_yield {α β : Type} (xs : List α) (s : β) (step : β → α → β) :
    (forIn (m := Id) xs s (fun a b => ForInStep.yield (step b a))) = xs.foldl step s :=
  List.forIn_pure_yield_eq_foldl (m := Id) (fun a b => step b a) s

/-- Normalize a conditional state update inside a loop. -/
theorem refined_forIn_conditional_update {α β : Type} (xs : List ℕ) (s : α × β)
    (insert : α → β → α) (next : β → β) (d : ℕ) :
    (forIn (m := Id) xs s (fun j s => if j + 1 < d then
      ForInStep.yield (insert s.1 s.2, next s.2) else
      ForInStep.yield (insert s.1 s.2, s.2))) =
    xs.foldl (fun s j => (insert s.1 s.2, if j + 1 < d then next s.2 else s.2)) s := by
  have h : (fun (j : ℕ) (s : α × β) => if j + 1 < d then
      ForInStep.yield (insert s.1 s.2, next s.2) else
      ForInStep.yield (insert s.1 s.2, s.2)) =
      (fun j s => ForInStep.yield (insert s.1 s.2, if j + 1 < d then next s.2 else s.2)) := by
    funext j s
    split <;> rfl
  rw [h]
  exact refined_forIn_yield xs s _

theorem paired_forIn_conditional_update {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (d : ℕ)
    (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) :
    (forIn (m := Id) (List.range d) s (fun j s => if j + 1 < d then
      ForInStep.yield (insertPairedColumn s.1 s.2,
        { top := A *ᵥ s.2.top, bottom := A *ᵥ s.2.bottom }) else
      ForInStep.yield (insertPairedColumn s.1 s.2, s.2))).1 =
    ((List.range d).foldl (fun s _ =>
      (insertPairedColumn s.1 s.2, { top := A *ᵥ s.2.top, bottom := A *ᵥ s.2.bottom })) s).1 := by
  have h := refined_forIn_conditional_update (List.range d) s insertPairedColumn
    (fun w => ({ top := A *ᵥ w.top, bottom := A *ᵥ w.bottom } : PairedColumn K n)) d
  rw [h, paired_krylov_skip_last]

/-- The imperative definition elaborates to the nested loop proof model. -/
theorem computeRefinedJordanKrylovBasis_eq_loops
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) (preprocess : Bool) :
    computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess =
      let U := fun j => if 1 ≤ j ∧ j ≤ ℓbar then V j else []
      let U := if preprocess then reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) U ℓbar else U
      let run := fun U B used D => refinedLoopResult
        (forIn (m := Id) (List.range ℓbar).reverse (none, U, B, used, D)
          (refinedLayerStep K A f m preprocess ℓbar) : Id (RefinedLoopState K n))
      match U ℓbar with
      | [] => run U ∅ 0 #[]
      | v :: rest =>
        if ℓbar = m then {v} else
          let D := ((List.range f.natDegree).foldl
            (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
              (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩))
            (#[], ⟨(PolynomialOperations.applyMatrix f A)^[ℓbar - 1] v, v⟩)).1
          run (Function.update U ℓbar rest) {v} ℓbar D := by
  let flag := preprocess
  have ht (v : Fin n → K) (k : ℕ) := iterate_loop_eq (PolynomialOperations.applyMatrix f A) v k
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind] at ht
  simp only [computeRefinedJordanKrylovBasis, refinedLoopResult, Id.run, List.forIn_map,
    Nat.succ_eq_add_one, Nat.add_sub_cancel, Bind.bind, Pure.pure]
  dsimp only [Pure.pure] at ht
  cases preprocess <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals simp only [paired_forIn_conditional_update, refined_forIn_yield, ht]
  all_goals split
  all_goals rename_i heq
  all_goals first | rw [heq] | (
    have hn {α : Type} (xs : List α) (h : ∀ v rest, xs = v :: rest → False) : xs = [] := by
      cases xs with
      | nil => rfl
      | cons v rest => exact False.elim (h v rest rfl)
    rw [hn _ heq])
  all_goals dsimp only
  all_goals by_cases hstop : ℓbar = m
  all_goals try simp only [ite_eq_left hstop]
  all_goals try simp only [ite_eq_right hstop]
  all_goals
    generalize ho : (forIn (m := Id) (List.range ℓbar).reverse _ _ : Id (RefinedLoopState K n)) = out
    conv_lhs at ho =>
      arg 3
      equals refinedLayerStep K A f m flag ℓbar =>
        funext k s
        dsimp only [refinedLayerStep, refinedCandidateStep, refinedPreprocess, flag]
        simp only [Bool.false_eq_true, eq_self, false_and, true_and, ite_false]
        by_cases hpre : k + 1 < ℓbar ∧ s.2.1 (k + 1) ≠ []
        all_goals try simp only [ite_eq_left hpre]
        all_goals try simp only [ite_eq_right hpre]
        all_goals
          generalize hi : (forIn (m := Id) (_ : List (Fin n → K)) _ _ : Id (RefinedLoopState K n)) = t
          conv_lhs at hi =>
            arg 3
            equals refinedCandidateStep K A f m k => rfl
          rw [hi]
          rcases t with ⟨result, pending, B, used, D⟩
          cases result <;> rfl
    rw [ho]
    rcases out with ⟨result, pending, B, used, D⟩
    cases result <;> rfl

/-- Initialization precedes the recursive model of the remaining loops. -/
theorem computeRefinedJordanKrylovBasis_eq_model
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) (preprocess : Bool) :
    computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess =
      let U := fun j => if 1 ≤ j ∧ j ≤ ℓbar then V j else []
      let U := if preprocess then reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) U ℓbar else U
      let run := fun U B used D => refinedElimination K A f m preprocess ℓbar ℓbar
        (U ℓbar) (Function.update U ℓbar []) B used D
      match U ℓbar with
      | [] => run U ∅ 0 #[]
      | v :: rest =>
        if ℓbar = m then {v} else
          let D := ((List.range f.natDegree).foldl
            (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
              (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩))
            (#[], ⟨(PolynomialOperations.applyMatrix f A)^[ℓbar - 1] v, v⟩)).1
          run (Function.update U ℓbar rest) {v} ℓbar D := by
  rw [computeRefinedJordanKrylovBasis_eq_loops]
  simp only [refined_outer_eq_model, refinedPreprocess, lt_self_iff_false, false_and, and_false, ite_false]

end SympyProofs.JordanKrylov
