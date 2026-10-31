module

public import SympyProofs.Sum.Gosper.Backend.Basic
public import SympyProofs.Sum.Gosper.Backend.Inverse
public import SympyProofs.Sum.Gosper.Backend.Residual

/-! Correctness of matrix construction and solution extraction through backend operations. -/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] {m n : ℕ}

/-- Filling a list of entries copies the target matrix at exactly those positions. -/
theorem Backend.setElement_foldl_apply (backend : Backend K) (h : backend.Valid)
    (entries : List (Fin m × Fin n)) (initial target : Matrix (Fin m) (Fin n) K)
    (i : Fin m) (j : Fin n) :
    (entries.foldl (fun M pos => backend.setElement M pos.1 pos.2 (target pos.1 pos.2))
      initial) i j = if (i, j) ∈ entries then target i j else initial i j := by
  induction entries generalizing initial with
  | nil => simp
  | cons pos entries ih =>
    rw [List.foldl_cons, ih, h.setElement_apply]
    by_cases hm : (i, j) ∈ entries
    · simp [hm]
    · by_cases hi : i = pos.1 <;> by_cases hj : j = pos.2 <;>
        simp_all [Prod.ext_iff]

/-- Writing each coefficient constructs the matrix independently of any right-hand side. -/
theorem Backend.fill_matrix_eq (backend : Backend K) (h : backend.Valid)
    (A : Matrix (Fin m) (Fin n) K) :
    (Id.run do
      let mut M := backend.zeros m n
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j (A i j)
      return M) = A := by
  let entries := (List.finRange m).flatMap fun i =>
    (List.finRange n).map fun j => (i, j)
  have he : (Id.run do
      let mut M := backend.zeros m n
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j (A i j)
      return M) =
      entries.foldl (fun M pos => backend.setElement M pos.1 pos.2 (A pos.1 pos.2))
        (backend.zeros m n) := by
    simp [entries, List.foldl_flatMap, List.foldl_map]
  rw [he]
  ext i j
  rw [backend.setElement_foldl_apply h]
  have hm : (i, j) ∈ entries := by simp [entries]
  simp [hm]

/-- Fill the coefficient block and identity diagonal in one pass to construct `[A | I]`. -/
theorem Backend.fill_identity_augmented_eq (backend : Backend K) (h : backend.Valid)
    (A : Matrix (Fin m) (Fin n) K) :
    (Id.run do
      let mut M := backend.zeros m (n + m)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i (j.castAdd m) (A i j)
        M := backend.setElement M i (Fin.natAdd n i) 1
      return M) = augmentedIdentity A := by
  let entries := (List.finRange m).flatMap fun i =>
    ((List.finRange n).map fun j => (i, j.castAdd m)) ++ [(i, Fin.natAdd n i)]
  have he : (Id.run do
      let mut M := backend.zeros m (n + m)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i (j.castAdd m) (A i j)
        M := backend.setElement M i (Fin.natAdd n i) 1
      return M) =
      entries.foldl (fun M pos =>
        backend.setElement M pos.1 pos.2 (augmentedIdentity A pos.1 pos.2))
        (backend.zeros m (n + m)) := by
    simp [entries, List.foldl_flatMap, List.foldl_append, List.foldl_map,
      augmentedIdentity]
  rw [he]
  ext i j
  rw [backend.setElement_foldl_apply h]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [entries, augmentedIdentity]
  · by_cases hij : i = j
    · subst j
      simp [entries, augmentedIdentity]
    · simp [entries, augmentedIdentity, h.zeros_eq, hij]

/-- Writing every coefficient column and then the right-hand side constructs `[A | b]`. -/
theorem Backend.fill_augmented_eq (backend : Backend K) (h : backend.Valid)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (Id.run do
      let mut M := backend.zeros m (n + 1)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j.castSucc (A i j)
        M := backend.setElement M i (Fin.last n) (b i)
      return M) = augmented A b := by
  let entries := (List.finRange m).flatMap fun i =>
    ((List.finRange n).map fun j => (i, j.castSucc)) ++ [(i, Fin.last n)]
  have he : (Id.run do
      let mut M := backend.zeros m (n + 1)
      for i in List.finRange m do
        for j in List.finRange n do
          M := backend.setElement M i j.castSucc (A i j)
        M := backend.setElement M i (Fin.last n) (b i)
      return M) =
      entries.foldl (fun M pos => backend.setElement M pos.1 pos.2 (augmented A b pos.1 pos.2))
        (backend.zeros m (n + 1)) := by
    simp [entries, List.foldl_flatMap, List.foldl_append, List.foldl_map, augmented]
  rw [he]
  ext i j
  rw [backend.setElement_foldl_apply h]
  have hm : (i, j) ∈ entries := by
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange i, ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp
  simp [hm]

/-- Read the augmented column once and reconstruct the polynomial from its pivot rows. -/
theorem Backend.reconstruct_eq [DecidableEq K] (backend : Backend K) (h : backend.Valid)
    (r : RrefResult K m (n + 1)) (hlast : Fin.last n ∉ r.pivots) :
    (Id.run do
      let rhs := backend.getCol r.matrix (Fin.last n)
      let mut x : Polynomial K := 0
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        x := x + Polynomial.monomial (pivot : ℕ) (rhs row / r.denominator)
      return x) = Polynomial.ofFn n r.solution := by
  rw [r.ofFn_solution_eq_pivots hlast, List.mapFinIdx_eq_zipIdx_map,
    List.sum_eq_foldl, List.foldl_map]
  simp [h.getCol_apply]

/-- The coefficient at a left pivot is read from its unique pivot row. -/
theorem RrefResult.leftSolution_apply_of_pivot {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A)
    (values : Fin m → K) (i : Fin m) (j : Fin n)
    (hp : r.pivots[i.val]? = some (j.castAdd m)) :
    r.leftSolution values j = values i / r.denominator := by
  unfold RrefResult.leftSolution
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

omit [Field K] in
private theorem update_pair_foldl_apply (entries : List (Fin n × Fin m))
    (initial : (Fin n → K) × (Fin m → K))
    (target : (Fin n → K) × (Fin m → K)) :
    entries.foldl (fun v p =>
      (Function.update v.1 p.1 (target.1 p.1), Function.update v.2 p.2 (target.2 p.2))) initial =
      ((fun j => if j ∈ entries.map Prod.fst then target.1 j else initial.1 j),
       (fun i => if i ∈ entries.map Prod.snd then target.2 i else initial.2 i)) := by
  induction entries generalizing initial with
  | nil => rfl
  | cons p entries ih =>
    rw [List.foldl_cons, ih]
    apply Prod.ext
    · funext j
      by_cases hm : j ∈ entries.map Prod.fst
      · simp [hm]
      · by_cases hj : j = p.1 <;> simp [hm, hj, Function.update]
    · funext i
      by_cases hm : i ∈ entries.map Prod.snd
      · simp [hm]
      · by_cases hi : i = p.2 <;> simp [hm, hi, Function.update]

/-- Read pivot coefficients and clear their transformed rows in one pass. -/
theorem RrefResult.extract_transformed_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → K) :
    (Id.run do
      let mut coefficients : Fin n → K := 0
      let mut residual := values
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := Function.update coefficients pivot (values row / r.denominator)
          residual := Function.update residual row 0
      return (coefficients, residual)) = (r.leftSolution values, r.leftResidual values) := by
  let entries : List (Fin n × Fin m) := r.pivots.zipIdx.attach.flatMap fun p =>
    if hp : p.val.1.val < n then
      [(⟨p.val.1.val, hp⟩,
        ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩)]
    else []
  have hvalue (p : {p // p ∈ r.pivots.zipIdx}) (hp : p.val.1.val < n) :
      values ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩ /
          r.denominator = r.leftSolution values ⟨p.val.1.val, hp⟩ := by
    symm
    apply r.leftSolution_apply_of_pivot hr
    simpa using List.mem_zipIdx_iff_getElem?.mp p.property
  have he : (Id.run do
      let mut coefficients : Fin n → K := 0
      let mut residual := values
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := Function.update coefficients pivot (values row / r.denominator)
          residual := Function.update residual row 0
      return (coefficients, residual)) =
      entries.foldl (fun (v : (Fin n → K) × (Fin m → K)) p =>
        (Function.update v.1 p.1 (r.leftSolution values p.1),
         Function.update v.2 p.2 0)) (0, values) := by
    simp [entries, List.foldl_flatMap]
    simp only [← apply_dite]
    simp only [List.forIn_pure_yield_eq_foldl]
    change List.foldl _ _ _ = List.foldl _ _ _
    congr 1
    funext acc p
    split_ifs with hp
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [hvalue p hp]
    · simp
  rw [he]
  refine (update_pair_foldl_apply entries (0, values)
    (r.leftSolution values, fun _ => 0)).trans ?_
  apply Prod.ext
  · funext j
    by_cases hm : j ∈ entries.map Prod.fst
    · simp [hm]
    · have hp : ∀ i : Fin m, r.pivots[i.val]? ≠ some (j.castAdd m) := by
        intro i hi
        apply hm
        apply List.mem_map.mpr
        refine ⟨(j, i), ?_, rfl⟩
        apply List.mem_flatMap.mpr
        refine ⟨⟨(j.castAdd m, i.val), List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩,
          List.mem_attach _ _, ?_⟩
        simp [j.isLt]
      simp [hm, RrefResult.leftSolution, hp]
  · funext i
    have hm : i ∈ entries.map Prod.snd ↔
        (r.pivots[i.val]?).any (fun p => decide (p.val < n)) := by
      constructor
      · intro hi
        obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hi
        obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hp
        split_ifs at hq with hqleft
        · simp only [List.mem_singleton] at hq
          subst p
          have hi' : q.val.2 = i.val := congrArg Fin.val hpi
          have hpivot := List.mem_zipIdx_iff_getElem?.mp q.property
          rw [hi'] at hpivot
          simp [hpivot, hqleft]
        · simp at hq
      · intro hi
        cases hp : r.pivots[i.val]? with
        | none => simp [hp] at hi
        | some p =>
          have hpn : p.val < n := by simpa [hp] using hi
          apply List.mem_map.mpr
          refine ⟨(⟨p.val, hpn⟩, i), ?_, rfl⟩
          apply List.mem_flatMap.mpr
          refine ⟨⟨(p, i.val), List.mk_mem_zipIdx_iff_getElem?.mpr hp⟩,
            List.mem_attach _ _, ?_⟩
          simp [hpn]
    simp only [RrefResult.leftResidual]
    simp [hm]

omit [Field K] in
private theorem vector_ofFn_set (v : Fin n → K) (i : Fin n) (value : K) :
    (Vector.ofFn v).set i.val value = Vector.ofFn (Function.update v i value) := by
  apply Vector.ext
  intro j hj
  simp [Vector.getElem_set, Function.update, Fin.ext_iff, eq_comm]

/-- Extract coefficients into fixed-size vectors and clear the corresponding residual rows. -/
theorem RrefResult.extract_transformed_vector_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → K) :
    (Id.run do
      let mut coefficients := Vector.replicate n (0 : K)
      let mut residual := Vector.ofFn values
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] / r.denominator)
          residual := residual.set row.val 0
      return (coefficients, residual)) =
      (Vector.ofFn (r.leftSolution values), Vector.ofFn (r.leftResidual values)) := by
  have hzero : Vector.replicate n (0 : K) = Vector.ofFn (0 : Fin n → K) := by
    apply Vector.ext
    intro i hi
    simp
  have he := congrArg (fun p : (Fin n → K) × (Fin m → K) =>
    (Vector.ofFn p.1, Vector.ofFn p.2)) (r.extract_transformed_eq hr values)
  rw [← he, hzero]
  simp
  simp only [← apply_dite, List.forIn_pure_yield_eq_foldl]
  change List.foldl _ _ _ =
    (fun p : (Fin n → K) × (Fin m → K) => (Vector.ofFn p.1, Vector.ofFn p.2))
      (List.foldl _ _ _)
  apply List.foldl_hom (fun p : (Fin n → K) × (Fin m → K) =>
    (Vector.ofFn p.1, Vector.ofFn p.2)) (init := (0, values))
  intro acc p
  rcases p with ⟨⟨pivot, row⟩, hp⟩
  split_ifs with h
  · have hrow : row < m := lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le
    exact Prod.ext (vector_ofFn_set acc.1 ⟨pivot.val, h⟩ _)
      (vector_ofFn_set acc.2 ⟨row, hrow⟩ _)
  · rfl

private theorem foldl_pair_eq {α β γ : Type*} (entries : List α)
    (f : β → α → β) (g : γ → α → γ) (b : β) (c : γ) :
    entries.foldl (fun p a => (f p.1 a, g p.2 a)) (b, c) =
      (entries.foldl f b, entries.foldl g c) := by
  induction entries generalizing b c with
  | nil => rfl
  | cons a entries ih => simp only [List.foldl_cons, ih]

/-- Keep pivot coefficients in a fixed-size vector and append only the remaining equations. -/
theorem RrefResult.extract_transformed_array_residual_eq
    {A : Matrix (Fin m) (Fin (n + m)) K}
    (r : RrefResult K m (n + m)) (hr : r.Valid A) (values : Fin m → K) :
    (Id.run do
      let mut coefficients := Vector.replicate n (0 : K)
      let mut residual := (#[] : Array K)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] / r.denominator)
        else
          residual := residual.push ((Vector.ofFn values)[row.val])
      return (coefficients, residual)) =
      (Vector.ofFn (r.leftSolution values), r.residualEntries values) := by
  let entries := r.pivots.zipIdx.attach
  let stepC (coefficients : Vector K n) (p : {p // p ∈ r.pivots.zipIdx}) : Vector K n :=
    if h : p.val.1.val < n then
      coefficients.set p.val.1.val
        (values ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩ /
          r.denominator) h
    else coefficients
  let stepR (residual : Array K) (p : {p // p ∈ r.pivots.zipIdx}) : Array K :=
    if p.val.1.val < n then residual else
      residual.push (values
        ⟨p.val.2, lt_of_lt_of_le (List.mem_zipIdx' p.property).1 r.length_le⟩)
  have hc : entries.foldl stepC (Vector.replicate n 0) =
      Vector.ofFn (r.leftSolution values) := by
    have old := congrArg Prod.fst (r.extract_transformed_vector_eq hr values)
    simp at old
    simp only [← apply_dite, List.forIn_pure_yield_eq_foldl] at old
    rw [← old]
    change List.foldl _ _ _ = Prod.fst (List.foldl _ _ _)
    apply List.foldl_hom Prod.fst
      (init := (Vector.replicate n (0 : K), Vector.ofFn values))
    intro acc p
    rcases p with ⟨⟨pivot, row⟩, hp⟩
    dsimp only [stepC]
    split_ifs <;> rfl
  have he : (Id.run do
      let mut coefficients := Vector.replicate n (0 : K)
      let mut residual := (#[] : Array K)
      for ⟨(pivot, row), hp⟩ in r.pivots.zipIdx.attach do
        let row : Fin m := ⟨row, lt_of_lt_of_le (List.mem_zipIdx' hp).1 r.length_le⟩
        if h : pivot.val < n then
          let pivot : Fin n := ⟨pivot.val, h⟩
          coefficients := coefficients.set pivot.val
            ((Vector.ofFn values)[row.val] / r.denominator)
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
  let selected (p : {p // p ∈ r.pivots.zipIdx}) : Option K :=
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
