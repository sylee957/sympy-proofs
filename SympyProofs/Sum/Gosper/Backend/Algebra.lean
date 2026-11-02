module

public import SympyProofs.Sum.Gosper.Backend.FieldExtension

/-! Apply a base-field reduction to coefficients in a commutative algebra.
Only the stored base-field denominator is inverted; the target algebra needs
neither division nor decidable equality. -/

@[expose] public section

namespace Gosper.Algorithm

@[simp]
theorem RrefResult.map_rightMatrix {K L : Type*} [CommRing K] [CommRing L] {m n : ℕ}
    (r : RrefResult K m (n + m)) (f : K →+* L) :
    (r.map f).rightMatrix = r.rightMatrix.map f := rfl

@[simp]
theorem RrefResult.map_inverse {K L : Type*} [Field K] [Field L] {m n : ℕ}
    (r : RrefResult K m (n + m)) (f : K →+* L) :
    (r.map f).inverse = r.inverse.map f := by
  ext j k
  simp [RrefResult.map, RrefResult.inverse, map_sum, apply_ite, map_div₀]
  rfl

@[simp]
theorem RrefResult.map_residualEntries {K L α : Type*} [CommRing K] [CommRing L] {m n : ℕ}
    (r : RrefResult K m (n + m)) (f : K →+* L) (values : Fin m → α) :
    (r.map f).residualEntries values = r.residualEntries values := rfl

private theorem set_ofFn {α : Type*} {m : ℕ} (values : Fin m → α)
    (i : Fin m) (value : α) :
    (Vector.ofFn values).set i.val value = Vector.ofFn (Function.update values i value) := by
  apply Vector.ext
  intro j hj
  simp [Vector.getElem_set, Function.update, Fin.ext_iff, eq_comm]

private theorem set_foldl_ofFn {α : Type*} {m : ℕ} (entries : List (Fin m))
    (initial target : Fin m → α) :
    entries.foldl (fun a i => a.set i.val (target i)) (Vector.ofFn initial) =
      Vector.ofFn (fun i => if i ∈ entries then target i else initial i) := by
  induction entries generalizing initial with
  | nil => simp
  | cons i entries ih =>
    rw [List.foldl_cons, set_ofFn, ih]
    congr 1
    funext j
    by_cases hm : j ∈ entries
    · simp [hm]
    · by_cases hj : j = i <;> simp [hm, hj, Function.update]

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {m n : ℕ}

/-- Read left-pivot coefficients using the inverse denominator computed in `K`. -/
def RrefResult.algebraLeftSolution (r : RrefResult K m (n + m)) (values : Fin m → R) :
    Fin n → R := fun j =>
  ∑ i : Fin m, if r.pivots[i.val]? = some (j.castAdd m) then
    values i * algebraMap K R r.denominator⁻¹ else 0

theorem RrefResult.algebraLeftSolution_apply_of_pivot
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → R)
    (i : Fin m) (j : Fin n) (hp : r.pivots[i.val]? = some (j.castAdd m)) :
    r.algebraLeftSolution values j = values i * algebraMap K R r.denominator⁻¹ := by
  unfold algebraLeftSolution
  rw [Finset.sum_eq_single i]
  · simp [hp]
  · intro l _ hli
    have hne : r.pivots[l.val]? ≠ some (j.castAdd m) := by
      intro hl
      apply hli
      apply Fin.ext
      exact hr.ordered.nodup.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp hl).1
        (hl.trans hp.symm)
    simp [hne]
  · simp

/-- The mapped generalized inverse equals transformation followed by pivot extraction. -/
theorem RrefResult.algebraInverse_mulVec (r : RrefResult K m (n + m)) (rhs : Fin m → R) :
    (r.inverse.map (algebraMap K R)).mulVec rhs =
      r.algebraLeftSolution ((r.rightMatrix.map (algebraMap K R)).mulVec rhs) := by
  ext j
  simp only [RrefResult.inverse, algebraLeftSolution, rightMatrix, Matrix.mulVec,
    dotProduct, Matrix.map_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : r.pivots[i.val]? = some (j.castAdd m)
  · simp [hp, div_eq_mul_inv, map_mul, mul_comm, mul_left_comm]
  · simp [hp]

/-- Compute the transformed right-hand side using the mapped right block. -/
theorem RrefResult.transform_rhs_algebra_vector_eq (r : RrefResult K m (n + m))
    (values : Fin m → R) :
    (Id.run do
      let mut transformed := Vector.replicate m (0 : R)
      for i in List.finRange m do
        let mut value := (0 : R)
        for k in List.finRange m do
          value := value + algebraMap K R (r.matrix i (Fin.natAdd n k)) * values k
        transformed := transformed.set i.val value
      return transformed) =
      Vector.ofFn ((r.rightMatrix.map (algebraMap K R)).mulVec values) := by
  have hsum (i : Fin m) :
      (List.finRange m).foldl
        (fun value k => value + algebraMap K R (r.matrix i (Fin.natAdd n k)) * values k) 0 =
      (r.rightMatrix.map (algebraMap K R)).mulVec values i := by
    rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.ofFn_eq_map, List.sum_ofFn]
    rfl
  have hz : Vector.replicate m (0 : R) = Vector.ofFn (fun _ : Fin m => (0 : R)) := by
    apply Vector.ext
    simp
  simp [hsum, hz]
  simpa only [List.mem_finRange, ↓reduceIte] using
    set_foldl_ofFn (List.finRange m) (fun _ => (0 : R))
      ((r.rightMatrix.map (algebraMap K R)).mulVec values)

/-- The coefficient-only extraction loop is valid over any commutative `K`-algebra. -/
theorem RrefResult.extract_algebra_coefficients_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → R) :
    (Id.run do
      let mut coefficients := Vector.replicate n (0 : R)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] * algebraMap K R r.denominator⁻¹)
      return coefficients) = Vector.ofFn (r.algebraLeftSolution values) := by
  let entries : List (Fin n) := r.pivots.zipIdx.attach.flatMap fun p =>
    if hp : p.val.1.val < n then [⟨p.val.1.val, hp⟩] else []
  have hvalue (p : {p // p ∈ r.pivots.zipIdx}) (hp : p.val.1.val < n) :
      values ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩ *
          algebraMap K R r.denominator⁻¹ = r.algebraLeftSolution values ⟨p.val.1.val, hp⟩ := by
    symm
    apply r.algebraLeftSolution_apply_of_pivot hr
    simpa using List.mem_zipIdx_iff_getElem?.mp p.property
  have hz : Vector.replicate n (0 : R) = Vector.ofFn (fun _ : Fin n => (0 : R)) := by
    apply Vector.ext
    simp
  have he : (Id.run do
      let mut coefficients := Vector.replicate n (0 : R)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] * algebraMap K R r.denominator⁻¹)
      return coefficients) =
      entries.foldl (fun v j => v.set j.val (r.algebraLeftSolution values j))
        (Vector.replicate n 0) := by
    simp [entries, List.foldl_flatMap]
    simp only [← apply_dite, List.forIn_pure_yield_eq_foldl]
    change List.foldl _ _ _ = List.foldl _ _ _
    congr 1
    funext acc p
    split_ifs with hp
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [hvalue p hp]
    · rfl
  rw [he, hz, set_foldl_ofFn]
  congr 1
  funext j
  by_cases hm : j ∈ entries
  · simp [hm]
  · have hp : ∀ i : Fin m, r.pivots[i.val]? ≠ some (j.castAdd m) := by
      intro i hi
      apply hm
      apply List.mem_flatMap.mpr
      refine ⟨⟨(j.castAdd m, i.val), List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩,
        List.mem_attach _ _, ?_⟩
      simp [j.isLt]
    simp [hm, algebraLeftSolution, hp]

private theorem foldl_pair_eq {α β γ : Type*} (entries : List α)
    (f : β → α → β) (g : γ → α → γ) (b : β) (c : γ) :
    entries.foldl (fun p a => (f p.1 a, g p.2 a)) (b, c) =
      (entries.foldl f b, entries.foldl g c) := by
  induction entries generalizing b c with
  | nil => rfl
  | cons a entries ih => simp only [List.foldl_cons, ih]

/-- Keep pivot coefficients in a fixed-size vector and append only the remaining equations. -/
theorem RrefResult.extract_algebra_vector_residual_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → R) :
    (Id.run do
      let mut coefficients := Vector.replicate n (0 : R)
      let mut residual := (#[] : Array R)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] * algebraMap K R r.denominator⁻¹)
        else
          residual := residual.push ((Vector.ofFn values)[row.val])
      return (coefficients, residual)) =
      (Vector.ofFn (r.algebraLeftSolution values), r.residualEntries values) := by
  let entries := r.pivots.zipIdx.attach
  let stepC (coefficients : Vector R n) (p : {p // p ∈ r.pivots.zipIdx}) : Vector R n :=
    if h : p.val.1.val < n then
      coefficients.set p.val.1.val
        (values ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩ *
          algebraMap K R r.denominator⁻¹) h
    else coefficients
  let stepR (residual : Array R) (p : {p // p ∈ r.pivots.zipIdx}) : Array R :=
    if p.val.1.val < n then residual else
      residual.push (values
        ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩)
  have hc : entries.foldl stepC (Vector.replicate n 0) =
      Vector.ofFn (r.algebraLeftSolution values) := by
    have old := r.extract_algebra_coefficients_eq hr values
    simp at old
    simp only [← apply_dite, List.forIn_pure_yield_eq_foldl] at old
    simpa only [entries, stepC, Id.run, pure] using old
  have he : (Id.run do
      let mut coefficients := Vector.replicate n (0 : R)
      let mut residual := (#[] : Array R)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] * algebraMap K R r.denominator⁻¹)
        else
          residual := residual.push ((Vector.ofFn values)[row.val])
      return (coefficients, residual)) =
      entries.foldl (fun acc p => (stepC acc.1 p, stepR acc.2 p))
        (Vector.replicate n 0, #[]) := by
    simp [entries]
    simp only [← apply_dite, List.forIn_pure_yield_eq_foldl]
    change List.foldl _ _ _ = List.foldl _ _ _
    congr 1
    funext acc p
    rcases p with ⟨⟨pivot, row⟩, hp⟩
    dsimp only [stepC, stepR]
    split_ifs <;> rfl
  rw [he, foldl_pair_eq, hc]
  congr 1
  let selected (p : {p // p ∈ r.pivots.zipIdx}) : Option R :=
    if p.val.1.val < n then none else some (values
      ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩)
  have hs : entries.foldl stepR #[] =
      (entries.filterMap selected).foldl Array.push #[] := by
    rw [List.foldl_filterMap]
    congr 1
    funext acc p
    dsimp only [stepR, selected]
    split_ifs <;> rfl
  rw [hs, List.foldl_push_eq_append']
  simp only [Array.empty_append]
  rfl

end Gosper.Algorithm
