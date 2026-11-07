module

public import Mathlib

/-! Proof model for the fraction-free vector elimination in `gosperSolve`.
The solver itself contains its forward and backward loops inline. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K L S : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable {m n : ℕ}

/-- The back substitution dot product uses an accumulator. -/
def directDot (a : Fin n → K) (x : Fin n → L) : L := Id.run do
  let mut value := 0
  for j in List.finRange n do
    value := value + algebraMap K L (a j) * x j
  return value

@[simp] theorem directDot_eq (a : Fin n → K) (x : Fin n → L) :
    directDot a x = ∑ j, algebraMap K L (a j) * x j := by
  have hsum : (List.finRange n).foldl
      (fun value j => value + algebraMap K L (a j) * x j) 0 =
      ∑ j, algebraMap K L (a j) * x j := by
    rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.ofFn_eq_map, List.sum_ofFn]
  simpa [directDot] using hsum

abbrev EliminationStep (K L : Type*) (n : ℕ) := Fin n × K × Vector K n × L

/-- A complete row update, including the now-zero pivot row. -/
def eliminationRows (A : Vector (Vector K n) m) (c : Fin n) (r : Fin m) :
    Vector (Vector K n) m :=
  let row := A[r.val]
  let p := row[c.val]
  A.map fun old =>
    let a := old[c.val]
    Vector.ofFn fun j : Fin n => p * old[j.val] - a * row[j.val]

/-- The same row operations on a right-hand side over an arbitrary algebra. -/
def eliminationRhs (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (r : Fin m) : Vector L m :=
  Vector.ofFn fun i : Fin m =>
    algebraMap K L (A[r.val][c.val]) * b[i.val] -
      algebraMap K L (A[i.val][c.val]) * b[r.val]

/-- Restore a pivot variable using the saved row; the additive update also works
for arbitrary intermediate numerators, without a support invariant. -/
def eliminationBackStep (step : EliminationStep K L n) (result : K × Vector L n) :
    K × Vector L n :=
  let value := algebraMap K L result.1 * step.2.2.2 -
    directDot (fun j : Fin n => step.2.2.1[j.val]) (fun j => result.2[j.val])
  let coefficients := result.2.map (fun x => algebraMap K L step.2.1 * x)
  (step.2.1 * result.1,
    coefficients.set step.1 (coefficients[step.1.val] + value))

/-- Recursive proof model for a list of remaining columns. The executable
algorithm uses the equivalent forward and backward loops below. -/
def eliminationColumns [DecidableEq K] (columns : List (Fin n))
    (A : Vector (Vector K n) m) (b : Vector L m) : K × Vector L n :=
  match columns with
  | [] => (1, Vector.replicate n 0)
  | c :: cs =>
      if h : ∃ r : Fin m, A[r.val][c.val] ≠ 0 then
        let r := Fin.find (fun r : Fin m => A[r.val][c.val] ≠ 0) h
        eliminationBackStep (c, A[r.val][c.val], A[r.val], b[r.val])
          (eliminationColumns cs (eliminationRows A c r) (eliminationRhs A b c r))
      else eliminationColumns cs A b

/-- One iteration of the forward loop, packaged only for the proof. -/
def eliminationForwardStep [DecidableEq K]
    (state : Vector (Vector K n) m × Vector L m × List (EliminationStep K L n))
    (c : Fin n) : Vector (Vector K n) m × Vector L m × List (EliminationStep K L n) :=
  if h : ∃ r : Fin m, state.1[r.val][c.val] ≠ 0 then
    let r := Fin.find (fun r : Fin m => state.1[r.val][c.val] ≠ 0) h
    (eliminationRows state.1 c r, eliminationRhs state.1 state.2.1 c r,
      (c, state.1[r.val][c.val], state.1[r.val], state.2.1[r.val]) :: state.2.2)
  else state

/-- Proof-only executable expression matching the loops in `gosperSolve`. -/
def eliminationRun [DecidableEq K] (A : Vector (Vector K n) m) (b : Vector L m) :
    K × Vector L n := Id.run do
  let mut A := A
  let mut b := b
  let mut steps : List (EliminationStep K L n) := []
  for c in List.finRange n do
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
        b := b.set i.val (algebraMap K L p * b[i.val] - algebraMap K L a * rhs)
        let updated := Id.run do
          let mut updated := source
          for j in List.finRange n do
            updated := updated.set j.val (p * source[j.val] - a * row[j.val])
          return updated
        A := A.set i.val updated
  let mut denominator := (1 : K)
  let mut coefficients := Vector.replicate n (0 : L)
  for step in steps do
    let value := algebraMap K L denominator * step.2.2.2 -
      directDot (fun j : Fin n => step.2.2.1[j.val]) (fun j => coefficients[j.val])
    coefficients := coefficients.map (fun x => algebraMap K L step.2.1 * x)
    coefficients := coefficients.set step.1 (coefficients[step.1.val] + value)
    denominator := step.2.1 * denominator
  return (denominator, coefficients)

/-- The matrix-function interface used in the correctness statement. -/
def eliminationModel [DecidableEq K] (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) :
    K × (Fin n → L) :=
  let result := eliminationRun (Vector.ofFn (fun i => Vector.ofFn (M i))) (Vector.ofFn b)
  (result.1, fun j => result.2[j.val])

theorem elimination_forward_backward [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (steps : List (EliminationStep K L n)) :
    ((columns.foldl eliminationForwardStep (A, b, steps)).2.2).foldl
        (fun result step => eliminationBackStep step result) (1, Vector.replicate n 0) =
      steps.foldl (fun result step => eliminationBackStep step result)
        (eliminationColumns columns A b) := by
  induction columns generalizing A b steps with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, eliminationForwardStep, eliminationColumns]
    split_ifs with h
    · exact ih _ _ _
    · exact ih _ _ _

/-- The imperative search stops at the first matching row. -/
theorem elimination_find_loop {α : Type*} (p : α → Prop) [DecidablePred p]
    (rows : List α) :
    (forIn rows none (fun r pivot =>
      if p r then pure (ForInStep.done (some r))
      else pure (ForInStep.yield pivot)) : Id (Option α)) =
      rows.find? (fun r => decide (p r)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : p r
    · simp [List.forIn_cons, h]
      rfl
    · simpa [List.forIn_cons, h] using ih

/-- The row scan agrees with the least-index pivot in the proof model. -/
theorem elimination_pivotLoop_eq (p : Fin m → Prop) [DecidablePred p] :
    (forIn (List.finRange m) none (fun r pivot =>
      if p r then pure (ForInStep.done (some r))
      else pure (ForInStep.yield pivot)) : Id (Option (Fin m))) =
      if h : ∃ r, p r then some (Fin.find p h) else none := by
  rw [elimination_find_loop]
  split_ifs with h
  · rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa only [decide_eq_true_eq] using Fin.find_spec h,
      (Fin.find p h).val, by simpa only [List.length_finRange] using (Fin.find p h).isLt,
      by simp only [List.getElem_finRange]; rfl, ?_⟩
    intro j hj
    have hmin := Fin.find_min h (j := ⟨j, lt_trans hj (Fin.find p h).isLt⟩) hj
    simpa using hmin
  · apply List.find?_eq_none.mpr
    intro r _
    simpa only [decide_eq_true_eq] using fun hp => h ⟨r, hp⟩

theorem elimination_pivotLoop_match {α : Sort*} (p : Fin m → Prop) [DecidablePred p]
    (found : Fin m → α) (missing : α) :
    (match (forIn (List.finRange m) none (fun r pivot =>
      if p r then pure (ForInStep.done (some r))
      else pure (ForInStep.yield pivot)) : Id (Option (Fin m))).run with
      | some r => found r
      | _x => missing) =
      if h : ∃ r, p r then found (Fin.find p h) else missing := by
  rw [elimination_pivotLoop_eq]
  split_ifs <;> rfl

/-- Setting each listed position to a fixed value leaves all other entries intact. -/
theorem elimination_fill_get {α : Type*} (indices : List (Fin n))
    (A : Vector α n) (f : Fin n → α) (j : Fin n) :
    (indices.foldl (fun current i => current.set i.val (f i)) A)[j.val] =
      if j ∈ indices then f j else A[j.val] := by
  induction indices generalizing A with
  | nil => rfl
  | cons i is ih =>
    by_cases hij : i = j
    · subst i
      simp only [List.foldl_cons, ih, List.mem_cons, true_or, ite_true,
        Vector.getElem_set_self]
      split_ifs <;> rfl
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases hmem : j ∈ is <;>
        simp [List.foldl_cons, ih, Ne.symm hij, hmem, hval]

theorem elimination_fill_eq {α : Type*} (A : Vector α n) (f : Fin n → α) :
    (List.finRange n).foldl (fun current i => current.set i.val (f i)) A =
      Vector.ofFn f := by
  ext j hj
  simpa using elimination_fill_get (List.finRange n) A f ⟨j, hj⟩


theorem elimination_joint_get {α β : Type*}
    (entries : List (Fin n)) (hn : entries.Nodup)
    (f : α → β → α × β) (initial : Vector α n × Vector β n) (i : Fin n) :
    let final := entries.foldl (fun current j =>
      let value := f current.1[j.val] current.2[j.val]
      (current.1.set j.val value.1, current.2.set j.val value.2)) initial
    (final.1[i.val], final.2[i.val]) =
      if i ∈ entries then f initial.1[i.val] initial.2[i.val]
      else (initial.1[i.val], initial.2[i.val]) := by
  induction entries generalizing initial with
  | nil => simp
  | cons j entries ih =>
    have hj : j ∉ entries := (List.nodup_cons.mp hn).1
    have ht : entries.Nodup := hn.of_cons
    dsimp only
    rw [List.foldl_cons, ih ht]
    by_cases hi : i = j
    · subst i
      simp [hj]
    · have hij : j.val ≠ i.val := by
        intro h
        exact hi (Fin.ext h.symm)
      simp [hi, hij]

theorem elimination_joint_foldl {α β : Type*} (f : α → β → α × β)
    (A : Vector α n) (b : Vector β n) :
    (List.finRange n).foldl (fun current i =>
      let value := f current.1[i.val] current.2[i.val]
      (current.1.set i.val value.1, current.2.set i.val value.2)) (A, b) =
        (Vector.ofFn (fun i => (f A[i.val] b[i.val]).1),
          Vector.ofFn (fun i => (f A[i.val] b[i.val]).2)) := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    have h := elimination_joint_get (List.finRange n) (List.nodup_finRange n)
      f (A, b) ⟨i, hi⟩
    simpa using congrArg Prod.fst h
  · apply Vector.ext
    intro i hi
    have h := elimination_joint_get (List.finRange n) (List.nodup_finRange n)
      f (A, b) ⟨i, hi⟩
    simpa using congrArg Prod.snd h

/-- A row traversal performs the same operation on the matrix and right-hand side. -/
theorem elimination_rows_rhs_foldl (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (p : K) (row : Vector K n) (rhs : L) :
    (List.finRange m).foldl (fun current i =>
      (current.1.set i.val (Vector.ofFn fun j : Fin n =>
        p * current.1[i.val][j.val] - current.1[i.val][c.val] * row[j.val]),
        current.2.set i.val (algebraMap K L p * current.2[i.val] -
          algebraMap K L (current.1[i.val][c.val]) * rhs))) (A, b) =
      (A.map (fun source => Vector.ofFn fun j : Fin n =>
        p * source[j.val] - source[c.val] * row[j.val]),
        Vector.ofFn (fun i : Fin m => algebraMap K L p * b[i.val] -
          algebraMap K L (A[i.val][c.val]) * rhs)) := by
  refine (elimination_joint_foldl
    (fun (source : Vector K n) (value : L) =>
      (Vector.ofFn (fun j : Fin n => p * source[j.val] - source[c.val] * row[j.val]),
        algebraMap K L p * value - algebraMap K L (source[c.val]) * rhs)) A b).trans ?_
  apply Prod.ext
  · ext i hi
    simp
  · rfl

theorem eliminationRun_eq_columns [DecidableEq K]
    (A : Vector (Vector K n) m) (b : Vector L m) :
    eliminationRun A b = eliminationColumns (List.finRange n) A b := by
  have hrun (v : Vector K n) : (pure v : Id (Vector K n)).run = v := rfl
  simp only [eliminationRun, bind_pure, elimination_fill_eq, pure_bind,
    elimination_pivotLoop_match, ← apply_dite, List.forIn_pure_yield_eq_foldl,
    hrun, elimination_rows_rhs_foldl]
  change ((List.finRange n).foldl eliminationForwardStep (A, b, [])).2.2.foldl
    (fun result step => eliminationBackStep step result) (1, Vector.replicate n 0) = _
  exact elimination_forward_backward (List.finRange n) A b []

theorem eliminationRows_mulVec (A : Vector (Vector K n) m)
    (b : Vector L m) (c : Fin n) (r : Fin m) (y : Vector L n)
    (h : ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) * y[j.val] = b[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n,
        algebraMap K L ((eliminationRows A c r)[i.val][j.val]) * y[j.val] =
      (eliminationRhs A b c r)[i.val] := by
  intro i
  simp only [eliminationRows, eliminationRhs, Vector.getElem_map, Vector.getElem_ofFn,
    map_sub, map_mul, sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h i, h r]

theorem eliminationBackStep_get (c : Fin n) (p : K) (row : Vector K n)
    (rhs : L) (d : K) (x : Vector L n) (j : Fin n) :
    (eliminationBackStep (c, p, row, rhs) (d, x)).2[j.val] =
      algebraMap K L p * x[j.val] + if j = c then
        algebraMap K L d * rhs - ∑ k : Fin n, algebraMap K L (row[k.val]) * x[k.val]
      else 0 := by
  by_cases h : j = c
  · subst j
    simp [eliminationBackStep]
  · have hc : c.val ≠ j.val := fun he => h (Fin.ext he.symm)
    simp [eliminationBackStep, h, hc]

theorem eliminationBackStep_correct (A : Vector (Vector K n) m)
    (b : Vector L m) (c : Fin n) (r : Fin m) (d : K) (x : Vector L n)
    (h : ∀ i : Fin m, ∑ j : Fin n,
        algebraMap K L ((eliminationRows A c r)[i.val][j.val]) * x[j.val] =
      algebraMap K L d * (eliminationRhs A b c r)[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) *
        (eliminationBackStep (c, A[r.val][c.val], A[r.val], b[r.val]) (d, x)).2[j.val] =
      algebraMap K L (A[r.val][c.val] * d) * b[i.val] := by
  intro i
  have hi := h i
  simp only [eliminationRows, eliminationRhs, Vector.getElem_map, Vector.getElem_ofFn,
    map_sub, map_mul, sub_mul, mul_assoc] at hi
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hi
  simp only [eliminationBackStep_get, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_mul]
  have hs : (∑ j : Fin n, algebraMap K L (A[i.val][j.val]) *
      (algebraMap K L (A[r.val][c.val]) * x[j.val])) =
      algebraMap K L (A[r.val][c.val]) *
        ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) * x[j.val] := by
    simp only [Finset.mul_sum, mul_left_comm]
  rw [hs]
  linear_combination hi

theorem eliminationColumns_complete [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (hz : ∀ j : Fin n, j ∉ columns → ∀ i : Fin m, A[i.val][j.val] = 0)
    (h : ∃ y : Vector L n, ∀ i : Fin m,
      ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) * y[j.val] = b[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) *
        (eliminationColumns columns A b).2[j.val] =
      algebraMap K L (eliminationColumns columns A b).1 * b[i.val] := by
  induction columns generalizing A b with
  | nil =>
    obtain ⟨y, hy⟩ := h
    intro i
    have hb : b[i.val] = 0 := by
      simpa [hz] using (hy i).symm
    simp [eliminationColumns, hb]
  | cons c cs ih =>
    simp only [eliminationColumns]
    split_ifs with hp
    · apply eliminationBackStep_correct
      apply ih
      · intro j hj i
        by_cases hc : j = c
        · subst j
          simp only [eliminationRows, Vector.getElem_map, Vector.getElem_ofFn]
          ring
        · have hj' : j ∉ c :: cs := by simp [hc, hj]
          simp only [eliminationRows, Vector.getElem_map, Vector.getElem_ofFn,
            hz j hj', mul_zero, sub_self]
      · obtain ⟨y, hy⟩ := h
        exact ⟨y, eliminationRows_mulVec A b c _ y hy⟩
    · apply ih
      · intro j hj i
        by_cases hc : j = c
        · subst j
          have hc : ∀ r : Fin m, A[r.val][c.val] = 0 := by
            simpa only [not_exists, not_not] using hp
          exact hc i
        · exact hz j (by simp [hc, hj]) i
      · exact h

/-- The returned numerator solves every consistent system after multiplication
by the returned denominator. No injectivity assumption on the target algebra is needed. -/
theorem eliminationModel_complete [DecidableEq K]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (h : ∃ y, (M.map (algebraMap K L)).mulVec y = b) :
    (M.map (algebraMap K L)).mulVec (eliminationModel M b).2 =
      algebraMap K L (eliminationModel M b).1 • b := by
  obtain ⟨y, hy⟩ := h
  have hc := eliminationColumns_complete (List.finRange n)
    (Vector.ofFn (fun i => Vector.ofFn (M i))) (Vector.ofFn b)
    (by simp) ⟨Vector.ofFn y, by
      intro i
      simpa [Matrix.mulVec, dotProduct, Matrix.map, Matrix.of_apply] using congrFun hy i⟩
  ext i
  simpa [eliminationModel, eliminationRun_eq_columns, Matrix.mulVec, dotProduct,
    Matrix.map, Matrix.of_apply] using hc i

theorem eliminationColumns_denominator_ne_zero [IsDomain K] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m) :
    (eliminationColumns columns A b).1 ≠ 0 := by
  induction columns generalizing A b with
  | nil => simp [eliminationColumns]
  | cons c cs ih =>
      simp only [eliminationColumns]
      split_ifs with h
      · exact mul_ne_zero (Fin.find_spec h) (ih _ _)
      · exact ih _ _

theorem eliminationRhs_map [CommRing S] [Algebra K S] (f : L →ₐ[K] S)
    (A : Vector (Vector K n) m) (b : Vector L m) (c : Fin n) (r : Fin m) :
    eliminationRhs A (b.map f) c r = (eliminationRhs A b c r).map f := by
  ext i hi
  simp [eliminationRhs]

theorem eliminationBackStep_map [CommRing S] [Algebra K S] (f : L →ₐ[K] S)
    (c : Fin n) (p : K) (row : Vector K n) (rhs : L) (d : K) (x : Vector L n) :
    eliminationBackStep (c, p, row, f rhs) (d, x.map f) =
      ((eliminationBackStep (c, p, row, rhs) (d, x)).1,
        (eliminationBackStep (c, p, row, rhs) (d, x)).2.map f) := by
  apply Prod.ext
  · rfl
  · ext j hj
    by_cases h : c.val = j <;> simp [eliminationBackStep, h]

theorem eliminationColumns_map [DecidableEq K] [CommRing S] [Algebra K S]
    (f : L →ₐ[K] S) (columns : List (Fin n))
    (A : Vector (Vector K n) m) (b : Vector L m) :
    eliminationColumns columns A (b.map f) =
      ((eliminationColumns columns A b).1, (eliminationColumns columns A b).2.map f) := by
  induction columns generalizing A b with
  | nil => simp [eliminationColumns]
  | cons c cs ih =>
      simp only [eliminationColumns]
      split_ifs with h
      · rw [eliminationRhs_map, ih]
        simpa only [Vector.getElem_map] using
          eliminationBackStep_map f c _ _ (b[(Fin.find _ h).val])
            (eliminationColumns cs (eliminationRows A c (Fin.find _ h))
              (eliminationRhs A b c (Fin.find _ h))).1
            (eliminationColumns cs (eliminationRows A c (Fin.find _ h))
              (eliminationRhs A b c (Fin.find _ h))).2
      · exact ih _ _

theorem eliminationModel_denominator_ne_zero [IsDomain K] [DecidableEq K]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) :
    (eliminationModel M b).1 ≠ 0 := by
  simpa [eliminationModel, eliminationRun_eq_columns] using
    eliminationColumns_denominator_ne_zero (List.finRange n)
      (Vector.ofFn (fun i => Vector.ofFn (M i))) (Vector.ofFn b)

theorem eliminationModel_map [DecidableEq K] [CommRing S] [Algebra K S]
    (f : L →ₐ[K] S) (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) :
    eliminationModel M (f ∘ b) =
      ((eliminationModel M b).1, f ∘ (eliminationModel M b).2) := by
  have hm := eliminationColumns_map f (List.finRange n)
    (Vector.ofFn (fun i => Vector.ofFn (M i))) (Vector.ofFn b)
  simp only [Vector.map_ofFn] at hm
  apply Prod.ext
  · simpa [eliminationModel, eliminationRun_eq_columns] using congrArg Prod.fst hm
  · funext j
    simpa [eliminationModel, eliminationRun_eq_columns] using
      congrArg (fun result : K × Vector S n => result.2[j.val]) hm

end Gosper.Algorithm
