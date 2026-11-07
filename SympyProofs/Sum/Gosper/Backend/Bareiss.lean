module

public import SympyProofs.Sum.Gosper.Backend.Elimination

/-! Exact-division Bareiss elimination and its algebraic correctness interface. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K L S : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable {m n : ℕ}

/-- Divide the cross-multiplied coefficient rows by the preceding successful pivot. -/
def bareissRows [Div K] (A : Vector (Vector K n) m) (c : Fin n) (r : Fin m)
    (previous : K) : Vector (Vector K n) m :=
  (eliminationRows A c r).map fun row => row.map (fun value => value / previous)

/-- Apply the same exact division to the parameter-valued right-hand side. -/
def bareissRhs [Div L] (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (r : Fin m) (previous : K) : Vector L m :=
  (eliminationRhs A b c r).map fun value => value / algebraMap K L previous

/-- Recursive Bareiss reference model. Skipping a zero column preserves the previous pivot. -/
def bareissColumns [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (previous : K) : K × Vector L n :=
  match columns with
  | [] => (1, Vector.replicate n 0)
  | c :: cs =>
    if h : ∃ r : Fin m, A[r.val][c.val] ≠ 0 then
      let r := Fin.find (fun r : Fin m => A[r.val][c.val] ≠ 0) h
      eliminationBackStep (c, A[r.val][c.val], A[r.val], b[r.val])
        (bareissColumns cs (bareissRows A c r previous)
          (bareissRhs A b c r previous) A[r.val][c.val])
    else bareissColumns cs A b previous

/-- Every performed division recovers its original numerator when multiplied by
its nonzero divisor. The condition places no consistency restriction on the right-hand side. -/
def BareissExactDivisions [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (previous : K) : Prop :=
  match columns with
  | [] => previous ≠ 0
  | c :: cs => previous ≠ 0 ∧
    if h : ∃ r : Fin m, A[r.val][c.val] ≠ 0 then
      let r := Fin.find (fun r : Fin m => A[r.val][c.val] ≠ 0) h
      (∀ i : Fin m, ∀ j : Fin n,
        previous * (bareissRows A c r previous)[i.val][j.val] =
          (eliminationRows A c r)[i.val][j.val]) ∧
      (∀ i : Fin m, algebraMap K L previous * (bareissRhs A b c r previous)[i.val] =
        (eliminationRhs A b c r)[i.val]) ∧
      BareissExactDivisions cs (bareissRows A c r previous)
        (bareissRhs A b c r previous) A[r.val][c.val]
    else BareissExactDivisions cs A b previous

/-- A forward step stores the pivot equation and advances the exact-division divisor. -/
def bareissForwardStep [Div K] [Div L] [DecidableEq K]
    (state : Vector (Vector K n) m × Vector L m × List (EliminationStep K L n) × K)
    (c : Fin n) : Vector (Vector K n) m × Vector L m × List (EliminationStep K L n) × K :=
  if h : ∃ r : Fin m, state.1[r.val][c.val] ≠ 0 then
    let r := Fin.find (fun r : Fin m => state.1[r.val][c.val] ≠ 0) h
    (bareissRows state.1 c r state.2.2.2,
      bareissRhs state.1 state.2.1 c r state.2.2.2,
      (c, state.1[r.val][c.val], state.1[r.val], state.2.1[r.val]) :: state.2.2.1,
      state.1[r.val][c.val])
  else state

/-- Matrix-function interface for the Bareiss reference model. -/
def bareissModel [Div K] [Div L] [DecidableEq K]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) : K × (Fin n → L) :=
  let result := bareissColumns (List.finRange n)
    (Vector.ofFn fun i => Vector.ofFn (M i)) (Vector.ofFn b) 1
  (result.1, fun j => result.2[j.val])

/-- Exact divisibility is sufficient for the quotient-recovery interface. -/
theorem bareiss_div_recover {T : Type*} [CommRing T] [Div T] [MulDivCancelClass T]
    {a p : T} (hp : p ≠ 0) (h : p ∣ a) : p * (a / p) = a := by
  obtain ⟨q, rfl⟩ := h
  rw [mul_div_cancel_left₀ q hp]

theorem bareiss_forward_backward [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (steps : List (EliminationStep K L n)) (previous : K) :
    ((columns.foldl bareissForwardStep (A, b, steps, previous)).2.2.1).foldl
      (fun result step => eliminationBackStep step result) (1, Vector.replicate n 0) =
      steps.foldl (fun result step => eliminationBackStep step result)
        (bareissColumns columns A b previous) := by
  induction columns generalizing A b steps previous with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, bareissForwardStep, bareissColumns]
    split_ifs with hp <;> exact ih _ _ _ _

theorem bareissColumns_denominator_ne_zero [IsDomain K] [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (previous : K) : (bareissColumns columns A b previous).1 ≠ 0 := by
  induction columns generalizing A b previous with
  | nil => simp [bareissColumns]
  | cons c cs ih =>
    simp only [bareissColumns]
    split_ifs with hp
    · exact mul_ne_zero (Fin.find_spec hp) (ih _ _ _)
    · exact ih _ _ _

theorem bareissModel_denominator_ne_zero [IsDomain K] [Div K] [Div L] [DecidableEq K]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) : (bareissModel M b).1 ≠ 0 := by
  exact bareissColumns_denominator_ne_zero _ _ _ _


theorem bareissForward_pivots_descending_of_pairwise [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m)
    (steps : List (EliminationStep K L n)) (previous : K)
    (hcolumns : columns.Pairwise (fun c d => c.val < d.val))
    (hsteps : steps.Pairwise (fun s t => t.1.val < s.1.val))
    (hbefore : ∀ c ∈ columns, ∀ step ∈ steps, step.1.val < c.val) :
    ((columns.foldl bareissForwardStep (A, b, steps, previous)).2.2.1).Pairwise
      (fun s t => t.1.val < s.1.val) := by
  induction columns generalizing A b steps previous with
  | nil => exact hsteps
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ := List.pairwise_cons.mp hcolumns
    simp only [List.foldl_cons, bareissForwardStep]
    split_ifs with hp
    · apply ih _ _ _ _ hcs
      · apply List.pairwise_cons.mpr
        exact ⟨fun step hs => hbefore c (by simp) step hs, hsteps⟩
      · intro d hd step hs
        rcases List.mem_cons.mp hs with hstep | hstep
        · subst step
          exact hc d hd
        · exact hbefore d (List.mem_cons_of_mem c hd) step hstep
    · apply ih _ _ _ _ hcs hsteps
      intro d hd step hs
      exact hbefore d (List.mem_cons_of_mem c hd) step hs

theorem bareissForward_pivots_descending [Div K] [Div L] [DecidableEq K]
    (A : Vector (Vector K n) m) (b : Vector L m) (previous : K) :
    (((List.finRange n).foldl bareissForwardStep (A, b, [], previous)).2.2.1).Pairwise
      (fun s t => t.1.val < s.1.val) := by
  apply bareissForward_pivots_descending_of_pairwise
  · exact List.pairwise_lt_finRange n
  · exact List.Pairwise.nil
  · simp

theorem bareiss_algebraMap_ne_zero [IsDomain K] [IsDomain L]
    [Module.IsTorsionFree K L] {a : K} (ha : a ≠ 0) : algebraMap K L a ≠ 0 := by
  intro h
  exact ha ((FaithfulSMul.algebraMap_injective K L) (h.trans (map_zero _).symm))

/-- A consistent system stays consistent after each exact Bareiss row operation. -/
theorem bareissRows_mulVec [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div K] [Div L] (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (r : Fin m) (previous : K) (hp : previous ≠ 0)
    (hrows : ∀ i : Fin m, ∀ j : Fin n,
      previous * (bareissRows A c r previous)[i.val][j.val] =
        (eliminationRows A c r)[i.val][j.val])
    (hrhs : ∀ i : Fin m, algebraMap K L previous * (bareissRhs A b c r previous)[i.val] =
      (eliminationRhs A b c r)[i.val])
    (y : Vector L n)
    (h : ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) * y[j.val] = b[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n,
        algebraMap K L ((bareissRows A c r previous)[i.val][j.val]) * y[j.val] =
      (bareissRhs A b c r previous)[i.val] := by
  intro i
  apply mul_left_cancel₀ (bareiss_algebraMap_ne_zero (L := L) hp)
  calc
    algebraMap K L previous *
        (∑ j : Fin n, algebraMap K L ((bareissRows A c r previous)[i.val][j.val]) * y[j.val]) =
        ∑ j : Fin n, algebraMap K L
          (previous * (bareissRows A c r previous)[i.val][j.val]) * y[j.val] := by
      simp only [map_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ j : Fin n, algebraMap K L ((eliminationRows A c r)[i.val][j.val]) * y[j.val] := by
      simp only [hrows]
    _ = (eliminationRhs A b c r)[i.val] := eliminationRows_mulVec A b c r y h i
    _ = algebraMap K L previous * (bareissRhs A b c r previous)[i.val] := (hrhs i).symm

/-- A solution of the divided system can be restored with the saved pivot equation. -/
theorem bareissBackStep_correct [Div K] [Div L]
    (A : Vector (Vector K n) m) (b : Vector L m) (c : Fin n) (r : Fin m)
    (previous d : K) (x : Vector L n)
    (hrows : ∀ i : Fin m, ∀ j : Fin n,
      previous * (bareissRows A c r previous)[i.val][j.val] =
        (eliminationRows A c r)[i.val][j.val])
    (hrhs : ∀ i : Fin m, algebraMap K L previous * (bareissRhs A b c r previous)[i.val] =
      (eliminationRhs A b c r)[i.val])
    (h : ∀ i : Fin m, ∑ j : Fin n,
        algebraMap K L ((bareissRows A c r previous)[i.val][j.val]) * x[j.val] =
      algebraMap K L d * (bareissRhs A b c r previous)[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) *
        (eliminationBackStep (c, A[r.val][c.val], A[r.val], b[r.val]) (d, x)).2[j.val] =
      algebraMap K L (A[r.val][c.val] * d) * b[i.val] := by
  apply eliminationBackStep_correct
  intro i
  calc
    (∑ j : Fin n, algebraMap K L ((eliminationRows A c r)[i.val][j.val]) * x[j.val]) =
        ∑ j : Fin n, algebraMap K L
          (previous * (bareissRows A c r previous)[i.val][j.val]) * x[j.val] := by
      simp only [hrows]
    _ = algebraMap K L previous *
        (∑ j : Fin n, algebraMap K L ((bareissRows A c r previous)[i.val][j.val]) * x[j.val]) := by
      simp only [map_mul, Finset.mul_sum, mul_assoc]
    _ = algebraMap K L previous *
        (algebraMap K L d * (bareissRhs A b c r previous)[i.val]) := by rw [h i]
    _ = algebraMap K L d * (eliminationRhs A b c r)[i.val] := by rw [← hrhs i]; ring


/-- Every consistent system is solved up to the nonzero returned scale. -/
theorem bareissColumns_complete [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div K] [Div L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m) (previous : K)
    (hexact : BareissExactDivisions columns A b previous)
    (hz : ∀ j : Fin n, j ∉ columns → ∀ i : Fin m, A[i.val][j.val] = 0)
    (h : ∃ y : Vector L n, ∀ i : Fin m,
      ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) * y[j.val] = b[i.val]) :
    ∀ i : Fin m, ∑ j : Fin n, algebraMap K L (A[i.val][j.val]) *
        (bareissColumns columns A b previous).2[j.val] =
      algebraMap K L (bareissColumns columns A b previous).1 * b[i.val] := by
  induction columns generalizing A b previous with
  | nil =>
    obtain ⟨y, hy⟩ := h
    have hb (i : Fin m) : b[i.val] = 0 := by simpa [hz] using (hy i).symm
    simp [bareissColumns, hb]
  | cons c cs ih =>
    simp only [bareissColumns]
    dsimp only [BareissExactDivisions] at hexact
    split_ifs at hexact ⊢ with hpivot
    · obtain ⟨hprev, hrows, hrhs, he⟩ := hexact
      apply bareissBackStep_correct _ _ _ _ previous _ _ hrows hrhs
      apply ih _ _ _ he
      · intro j hj i
        apply mul_left_cancel₀ hprev
        rw [hrows i j, mul_zero]
        by_cases hc : j = c
        · subst j
          simp only [eliminationRows, Vector.getElem_map, Vector.getElem_ofFn]
          ring
        · simp only [eliminationRows, Vector.getElem_map, Vector.getElem_ofFn,
            hz j (by simp [hc, hj]), mul_zero, sub_self]
      · obtain ⟨y, hy⟩ := h
        exact ⟨y, bareissRows_mulVec A b c _ previous hprev hrows hrhs y hy⟩
    · apply ih _ _ _ hexact.2
      · intro j hj i
        by_cases hc : j = c
        · subst j
          have hc : ∀ r : Fin m, A[r.val][c.val] = 0 := by
            simpa only [not_exists, not_not] using hpivot
          exact hc i
        · exact hz j (by simp [hc, hj]) i
      · exact h

theorem bareissModel_complete [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div K] [Div L] [DecidableEq K]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (hexact : BareissExactDivisions (List.finRange n)
      (Vector.ofFn fun i => Vector.ofFn (M i)) (Vector.ofFn b) 1)
    (h : ∃ y, (M.map (algebraMap K L)).mulVec y = b) :
    (M.map (algebraMap K L)).mulVec (bareissModel M b).2 =
      algebraMap K L (bareissModel M b).1 • b := by
  obtain ⟨y, hy⟩ := h
  have hc := bareissColumns_complete (List.finRange n)
    (Vector.ofFn fun i => Vector.ofFn (M i)) (Vector.ofFn b) 1 hexact
    (by simp) ⟨Vector.ofFn y, by
      intro i
      simpa [Matrix.mulVec, dotProduct, Matrix.map, Matrix.of_apply] using congrFun hy i⟩
  ext i
  simpa [bareissModel, Matrix.mulVec, dotProduct, Matrix.map, Matrix.of_apply] using hc i

/-- Mapping an exact right-hand-side quotient commutes with specialization. -/
theorem bareissRhs_map [IsDomain K] [Div K] [Div L]
    [CommRing S] [IsDomain S] [Algebra K S] [Module.IsTorsionFree K S]
    [Div S] [MulDivCancelClass S]
    (f : L →ₐ[K] S) (A : Vector (Vector K n) m) (b : Vector L m)
    (c : Fin n) (r : Fin m) (previous : K) (hp : previous ≠ 0)
    (hrhs : ∀ i : Fin m, algebraMap K L previous * (bareissRhs A b c r previous)[i.val] =
      (eliminationRhs A b c r)[i.val]) :
    bareissRhs A (b.map f) c r previous = (bareissRhs A b c r previous).map f := by
  unfold bareissRhs
  rw [eliminationRhs_map f]
  ext i hi
  simp only [Vector.getElem_map]
  have he := congrArg f (hrhs ⟨i, hi⟩)
  simp only [map_mul, AlgHom.commutes] at he
  rw [← he]
  simpa only [bareissRhs, Vector.getElem_map] using
    mul_div_cancel_left₀ (f ((bareissRhs A b c r previous)[i]))
      (bareiss_algebraMap_ne_zero (L := S) hp)

theorem bareissColumns_map [IsDomain K] [Div K] [Div L] [DecidableEq K]
    [CommRing S] [IsDomain S] [Algebra K S] [Module.IsTorsionFree K S]
    [Div S] [MulDivCancelClass S]
    (f : L →ₐ[K] S) (columns : List (Fin n))
    (A : Vector (Vector K n) m) (b : Vector L m) (previous : K)
    (hexact : BareissExactDivisions columns A b previous) :
    bareissColumns columns A (b.map f) previous =
      ((bareissColumns columns A b previous).1, (bareissColumns columns A b previous).2.map f) := by
  induction columns generalizing A b previous with
  | nil => simp [bareissColumns]
  | cons c cs ih =>
    simp only [bareissColumns]
    dsimp only [BareissExactDivisions] at hexact
    split_ifs at hexact ⊢ with hpivot
    · obtain ⟨hprev, _, hrhs, he⟩ := hexact
      rw [bareissRhs_map f A b c _ previous hprev hrhs, ih _ _ _ he]
      simpa only [Vector.getElem_map] using
        eliminationBackStep_map f c _ _ (b[(Fin.find _ hpivot).val])
          (bareissColumns cs (bareissRows A c (Fin.find _ hpivot) previous)
            (bareissRhs A b c (Fin.find _ hpivot) previous)
            A[(Fin.find _ hpivot).val][c.val]).1
          (bareissColumns cs (bareissRows A c (Fin.find _ hpivot) previous)
            (bareissRhs A b c (Fin.find _ hpivot) previous)
            A[(Fin.find _ hpivot).val][c.val]).2
    · exact ih _ _ _ hexact.2

theorem bareissModel_map [IsDomain K] [Div K] [Div L] [DecidableEq K]
    [CommRing S] [IsDomain S] [Algebra K S] [Module.IsTorsionFree K S]
    [Div S] [MulDivCancelClass S]
    (f : L →ₐ[K] S) (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (hexact : BareissExactDivisions (List.finRange n)
      (Vector.ofFn fun i => Vector.ofFn (M i)) (Vector.ofFn b) 1) :
    bareissModel M (f ∘ b) = ((bareissModel M b).1, f ∘ (bareissModel M b).2) := by
  have hm := bareissColumns_map f (List.finRange n)
    (Vector.ofFn fun i => Vector.ofFn (M i)) (Vector.ofFn b) 1 hexact
  simp only [Vector.map_ofFn] at hm
  apply Prod.ext
  · simpa [bareissModel] using congrArg Prod.fst hm
  · funext j
    simpa [bareissModel] using congrArg (fun result : K × Vector S n => result.2[j.val]) hm


/-- Divisibility of the raw coefficient numerators gives the matrix recovery condition. -/
theorem bareissRows_exact_of_dvd [Div K] [MulDivCancelClass K]
    (A : Vector (Vector K n) m) (c : Fin n) (r : Fin m) (previous : K)
    (hp : previous ≠ 0)
    (h : ∀ i : Fin m, ∀ j : Fin n, previous ∣ (eliminationRows A c r)[i.val][j.val]) :
    ∀ i : Fin m, ∀ j : Fin n,
      previous * (bareissRows A c r previous)[i.val][j.val] =
        (eliminationRows A c r)[i.val][j.val] := by
  intro i j
  simpa only [bareissRows, Vector.getElem_map] using bareiss_div_recover hp (h i j)

/-- Divisibility of the augmented-column numerators gives right-hand-side recovery. -/
theorem bareissRhs_exact_of_dvd [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div L] [MulDivCancelClass L]
    (A : Vector (Vector K n) m) (b : Vector L m) (c : Fin n) (r : Fin m) (previous : K)
    (hp : previous ≠ 0)
    (h : ∀ i : Fin m, algebraMap K L previous ∣ (eliminationRhs A b c r)[i.val]) :
    ∀ i : Fin m, algebraMap K L previous * (bareissRhs A b c r previous)[i.val] =
      (eliminationRhs A b c r)[i.val] := by
  intro i
  simpa only [bareissRhs, Vector.getElem_map] using
    bareiss_div_recover (bareiss_algebraMap_ne_zero (L := L) hp) (h i)

/-- Exact divisions remain exact after a parameter map faithful on the pivot domain. -/
theorem BareissExactDivisions.map [IsDomain K] [Div K] [Div L] [DecidableEq K]
    [CommRing S] [IsDomain S] [Algebra K S] [Module.IsTorsionFree K S]
    [Div S] [MulDivCancelClass S]
    (f : L →ₐ[K] S) (columns : List (Fin n))
    (A : Vector (Vector K n) m) (b : Vector L m) (previous : K)
    (hexact : BareissExactDivisions columns A b previous) :
    BareissExactDivisions columns A (b.map f) previous := by
  induction columns generalizing A b previous with
  | nil => exact hexact
  | cons c cs ih =>
    simp only [BareissExactDivisions] at hexact ⊢
    split_ifs at hexact ⊢ with hpivot
    · obtain ⟨hprev, hrows, hrhs, he⟩ := hexact
      refine ⟨hprev, hrows, ?_, ?_⟩
      · intro i
        rw [bareissRhs_map f A b c _ previous hprev hrhs, eliminationRhs_map f]
        simpa only [Vector.getElem_map, map_mul, AlgHom.commutes] using congrArg f (hrhs i)
      · rw [bareissRhs_map f A b c _ previous hprev hrhs]
        exact ih _ _ _ he
    · exact ⟨hexact.1, ih _ _ _ hexact.2⟩

end Gosper.Algorithm
