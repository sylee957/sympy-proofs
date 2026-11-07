module

public import SympyProofs.Sum.Gosper.Backend.Bareiss
public import SympyProofs.Sum.Gosper.Backend.BareissExact

/-! Every Bareiss division is exact, including parameter-valued augmented columns. -/

@[expose] public section
noncomputable section

universe u

namespace Gosper.Algorithm

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable {m n : ℕ}

/-- Augment the original coefficient matrix by the parameter-valued right-hand side. -/
def bareissAugmented (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) :
    Matrix (Fin m) (Fin n ⊕ Unit) L :=
  Matrix.fromCols (M.map (algebraMap K L)) (fun i _ => b i)

/-- Coefficient rows after a history of successful pivots are bordered minors. -/
def bareissHistoryRows {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (rows : α → Fin m) (cols : α → Fin n) :
    Vector (Vector K n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => bareissMinor M rows cols i j

/-- The augmented column follows the same bordered-minor formula. -/
def bareissHistoryRhs {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (rows : α → Fin m) (cols : α → Fin n) : Vector L m :=
  Vector.ofFn fun i =>
    bareissMinor (bareissAugmented M b) rows (Sum.inl ∘ cols) i (Sum.inr ())

theorem bareissAugmented_core {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (rows : α → Fin m) (cols : α → Fin n) :
    ((bareissAugmented M b).submatrix rows (Sum.inl ∘ cols)).det =
      algebraMap K L (M.submatrix rows cols).det := by
  rw [RingHom.map_det]
  rfl

theorem bareissAugmented_minor {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (rows : α → Fin m) (cols : α → Fin n) (i : Fin m) (j : Fin n) :
    bareissMinor (bareissAugmented M b) rows (Sum.inl ∘ cols) i (Sum.inl j) =
      algebraMap K L (bareissMinor M rows cols i j) := by
  unfold bareissMinor
  rw [RingHom.map_det]
  congr 1
  ext a b
  cases a <;> cases b <;> rfl

/-- The mixed coefficient/RHS numerator is another instance of the same minor identity. -/
theorem bareissHistoryRhs_numerator [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (rows : α → Fin m) (cols : α → Fin n)
    (hp : (M.submatrix rows cols).det ≠ 0) (c : Fin n) (r i : Fin m) :
    (eliminationRhs (bareissHistoryRows M rows cols) (bareissHistoryRhs M b rows cols) c r)[i.val] =
      algebraMap K L (M.submatrix rows cols).det *
        (bareissHistoryRhs M b (Sum.elim rows (fun _ : Unit => r))
          (Sum.elim cols (fun _ : Unit => c)))[i.val] := by
  have hcore : ((bareissAugmented M b).submatrix rows (Sum.inl ∘ cols)).det ≠ 0 := by
    rw [bareissAugmented_core]
    exact bareiss_algebraMap_ne_zero hp
  have h := bareissMinor_step (bareissAugmented M b) rows (Sum.inl ∘ cols)
    hcore r i (Sum.inl c) (Sum.inr ())
  have hcols : Sum.elim (Sum.inl ∘ cols) (fun _ : Unit => (Sum.inl c : Fin n ⊕ Unit)) =
      Sum.inl ∘ Sum.elim cols (fun _ : Unit => c) := by
    funext a
    cases a <;> rfl
  rw [hcols, bareissAugmented_core, bareissAugmented_minor, bareissAugmented_minor] at h
  simpa only [eliminationRhs, bareissHistoryRows, bareissHistoryRhs, Vector.getElem_ofFn] using h

theorem bareissHistoryRows_step [IsDomain K] [Div K] [MulDivCancelClass K]
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (rows : α → Fin m) (cols : α → Fin n)
    (hp : (M.submatrix rows cols).det ≠ 0) (c : Fin n) (r : Fin m) :
    bareissRows (bareissHistoryRows M rows cols) c r (M.submatrix rows cols).det =
      bareissHistoryRows M (Sum.elim rows (fun _ : Unit => r))
        (Sum.elim cols (fun _ : Unit => c)) := by
  ext i hi j hj
  simp only [bareissRows, eliminationRows, bareissHistoryRows,
    Vector.getElem_map, Vector.getElem_ofFn]
  rw [bareissMinor_step M rows cols hp]
  exact mul_div_cancel_left₀ _ hp

theorem bareissHistoryRhs_step [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div L] [MulDivCancelClass L]
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L)
    (rows : α → Fin m) (cols : α → Fin n)
    (hp : (M.submatrix rows cols).det ≠ 0) (c : Fin n) (r : Fin m) :
    bareissRhs (bareissHistoryRows M rows cols) (bareissHistoryRhs M b rows cols)
        c r (M.submatrix rows cols).det =
      bareissHistoryRhs M b (Sum.elim rows (fun _ : Unit => r))
        (Sum.elim cols (fun _ : Unit => c)) := by
  ext i hi
  simp only [bareissRhs, Vector.getElem_map]
  rw [bareissHistoryRhs_numerator M b rows cols hp c r ⟨i, hi⟩]
  exact mul_div_cancel_left₀ _ (bareiss_algebraMap_ne_zero (L := L) hp)


set_option backward.isDefEq.respectTransparency false in
/-- Every state represented by pivot-history minors satisfies all remaining exact divisions. -/
theorem bareiss_history_exact [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div K] [Div L] [MulDivCancelClass K] [MulDivCancelClass L] [DecidableEq K]
    (columns : List (Fin n)) (M : Matrix (Fin m) (Fin n) K) (b : Fin m → L) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (rows : α → Fin m) (cols : α → Fin n),
      (M.submatrix rows cols).det ≠ 0 →
      BareissExactDivisions columns (bareissHistoryRows M rows cols)
        (bareissHistoryRhs M b rows cols) (M.submatrix rows cols).det := by
  induction columns with
  | nil =>
    intro α _ _ rows cols hp
    exact hp
  | cons c cs ih =>
    intro α _ _ rows cols hp
    simp only [BareissExactDivisions]
    refine ⟨hp, ?_⟩
    split_ifs with h
    · let r := Fin.find
        (fun r : Fin m => (bareissHistoryRows M rows cols)[r.val][c.val] ≠ 0) h
      change
        (∀ i : Fin m, ∀ j : Fin n, (M.submatrix rows cols).det *
          (bareissRows (bareissHistoryRows M rows cols) c r
            (M.submatrix rows cols).det)[i.val][j.val] =
          (eliminationRows (bareissHistoryRows M rows cols) c r)[i.val][j.val]) ∧
        (∀ i : Fin m, algebraMap K L (M.submatrix rows cols).det *
          (bareissRhs (bareissHistoryRows M rows cols) (bareissHistoryRhs M b rows cols)
            c r (M.submatrix rows cols).det)[i.val] =
          (eliminationRhs (bareissHistoryRows M rows cols) (bareissHistoryRhs M b rows cols)
            c r)[i.val]) ∧
        BareissExactDivisions cs
          (bareissRows (bareissHistoryRows M rows cols) c r (M.submatrix rows cols).det)
          (bareissRhs (bareissHistoryRows M rows cols) (bareissHistoryRhs M b rows cols)
            c r (M.submatrix rows cols).det)
          (bareissHistoryRows M rows cols)[r.val][c.val]
      have hpivotRaw : (bareissHistoryRows M rows cols)[r.val][c.val] ≠ 0 := Fin.find_spec h
      have hpivot : bareissMinor M rows cols r c ≠ 0 := by
        simpa only [bareissHistoryRows, Vector.getElem_ofFn] using hpivotRaw
      have hrows := bareissHistoryRows_step M rows cols hp c r
      have hrhs := bareissHistoryRhs_step M b rows cols hp c r
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        rw [hrows]
        simpa only [eliminationRows, bareissHistoryRows,
          Vector.getElem_map, Vector.getElem_ofFn] using
          (bareissMinor_step M rows cols hp r i c j).symm
      · intro i
        rw [hrhs]
        exact (bareissHistoryRhs_numerator M b rows cols hp c r i).symm
      · rw [hrows, hrhs]
        have hnew : (M.submatrix (Sum.elim rows (fun _ : Unit => r))
            (Sum.elim cols (fun _ : Unit => c))).det ≠ 0 := by
          rw [bareissMinor_core]
          exact hpivot
        have hrec := ih (Sum.elim rows (fun _ : Unit => r))
          (Sum.elim cols (fun _ : Unit => c)) hnew
        simpa only [bareissMinor_core, bareissHistoryRows, Vector.getElem_ofFn] using hrec
    · exact ih rows cols hp

/-- Bareiss elimination starts with empty histories and divisor one, so every
coefficient and parameter-valued right-hand-side division is exact. -/
theorem bareiss_exactDivisions [IsDomain K] [IsDomain L] [Module.IsTorsionFree K L]
    [Div K] [Div L] [MulDivCancelClass K] [MulDivCancelClass L] [DecidableEq K]
    (columns : List (Fin n)) (A : Vector (Vector K n) m) (b : Vector L m) :
    BareissExactDivisions columns A b 1 := by
  let M : Matrix (Fin m) (Fin n) K := fun i j => A[i.val][j.val]
  let b₀ : Fin m → L := fun i => b[i.val]
  have h := bareiss_history_exact columns M b₀
    (Fin.elim0 : Fin 0 → Fin m) (Fin.elim0 : Fin 0 → Fin n) (by simp)
  have hA : bareissHistoryRows M (Fin.elim0 : Fin 0 → Fin m)
      (Fin.elim0 : Fin 0 → Fin n) = A := by
    ext i hi j hj
    simpa only [bareissHistoryRows, Vector.getElem_ofFn, M] using
      bareissMinor_empty M ⟨i, hi⟩ ⟨j, hj⟩
  have hcols : Sum.inl ∘ (Fin.elim0 : Fin 0 → Fin n) =
      (Fin.elim0 : Fin 0 → Fin n ⊕ Unit) := by
    funext i
    exact i.elim0
  have hb : bareissHistoryRhs M b₀ (Fin.elim0 : Fin 0 → Fin m)
      (Fin.elim0 : Fin 0 → Fin n) = b := by
    ext i hi
    simp only [bareissHistoryRhs, Vector.getElem_ofFn, hcols]
    exact bareissMinor_empty (bareissAugmented M b₀) ⟨i, hi⟩ (Sum.inr ())
  rw [hA, hb] at h
  simpa using h

end Gosper.Algorithm
