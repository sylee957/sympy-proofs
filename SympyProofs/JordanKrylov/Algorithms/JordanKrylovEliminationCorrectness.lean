import SympyProofs.JordanKrylov.Algorithms.JordanKrylovElimination

/-! # Correctness of simultaneous column elimination

Reduction preserves the relation between paired halves and detects membership
in the upper-column span. Insertion preserves echelon form and extends that span.
-/
namespace SympyProofs.JordanKrylov

/-- Remark 4: a vanishing upper remainder certifies that its lower half
lies in the kernel of the map relating the two halves. -/
theorem PairedColumn.bottom_mem_ker {K : Type*} [Field K] {n : ℕ}
    (F : Module.End K (Fin n → K)) (r : PairedColumn K n)
    (hr : r.top = F r.bottom) (hz : r.top = 0) :
    r.bottom ∈ LinearMap.ker F := by
  exact hr.symm.trans hz

/-- The imperative reduction loop is a left fold of simultaneous subtractions. -/
theorem reducePairedColumn_eq_foldl {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    reducePairedColumn D v = D.toList.foldl
      (fun r iw =>
        let c := r.top iw.1 / iw.2.top iw.1
        { top := r.top - c • iw.2.top, bottom := r.bottom - c • iw.2.bottom }) v := by
  simp [reducePairedColumn, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]

/-- The relation between upper and lower blocks survives the entire reduction. -/
theorem reducePairedColumn_top_eq {K : Type*} [Field K] {n : ℕ}
    (F : Module.End K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = F iw.2.bottom)
    (hv : v.top = F v.bottom) :
    (reducePairedColumn D v).top = F (reducePairedColumn D v).bottom := by
  rw [reducePairedColumn_eq_foldl]
  generalize D.toList = ds at *
  induction ds generalizing v with
  | nil => exact hv
  | cons iw ds ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [hv, hD iw List.mem_cons_self]
    · intro jw hjw
      exact hD jw (List.mem_cons_of_mem _ hjw)

/-- Subtraction during elimination does not leave a subspace containing both
lower vectors. -/
theorem reducePairedColumn_bottom_mem {K : Type*} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.bottom ∈ W) (hv : v.bottom ∈ W) :
    (reducePairedColumn D v).bottom ∈ W := by
  rw [reducePairedColumn_eq_foldl]
  generalize D.toList = ds at *
  induction ds generalizing v with
  | nil => exact hv
  | cons iw ds ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact W.sub_mem hv (W.smul_mem _ (hD iw List.mem_cons_self))
    · intro jw hjw
      exact hD jw (List.mem_cons_of_mem _ hjw)

/-- The original lower vector and its remainder differ by a combination of
stored lower columns. This is the generation-preservation invariant. -/
theorem reducePairedColumn_bottom_sub_mem {K : Type*} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.bottom ∈ W) :
    v.bottom - (reducePairedColumn D v).bottom ∈ W := by
  rw [reducePairedColumn_eq_foldl]
  generalize D.toList = ds at *
  induction ds generalizing v with
  | nil => simp
  | cons iw ds ih =>
    simp only [List.foldl_cons]
    have h := ih {
      top := v.top - (v.top iw.1 / iw.2.top iw.1) • iw.2.top
      bottom := v.bottom - (v.top iw.1 / iw.2.top iw.1) • iw.2.bottom }
      (fun jw hjw => hD jw (List.mem_cons_of_mem _ hjw))
    have hc := W.smul_mem (v.top iw.1 / iw.2.top iw.1) (hD iw List.mem_cons_self)
    have ha := W.add_mem hc h
    convert ha using 1
    dsimp only
    abel

/-- The linear map on upper vectors represented by the reduction loop. -/
noncomputable def pairedTopReduction {K : Type*} [Field K] {n : ℕ} :
    List (Fin n × PairedColumn K n) → Module.End K (Fin n → K)
  | [] => LinearMap.id
  | iw :: ds => (pairedTopReduction ds).comp
      (LinearMap.id - (LinearMap.proj iw.1).smulRight
        ((iw.2.top iw.1)⁻¹ • iw.2.top))

@[simp] theorem pairedTopReduction_cons_apply {K : Type*} [Field K] {n : ℕ}
    (iw : Fin n × PairedColumn K n) (ds : List (Fin n × PairedColumn K n))
    (v : Fin n → K) :
    pairedTopReduction (iw :: ds) v =
      pairedTopReduction ds (v - (v iw.1 / iw.2.top iw.1) • iw.2.top) := by
  simp [pairedTopReduction, div_eq_mul_inv, smul_smul]

/-- The abstract linear map agrees with the executable upper-block reduction. -/
theorem reducePairedColumn_top_eq_linear {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    (reducePairedColumn D v).top = pairedTopReduction D.toList v.top := by
  rw [reducePairedColumn_eq_foldl]
  generalize D.toList = ds
  induction ds generalizing v with
  | nil => rfl
  | cons iw ds ih =>
    rw [List.foldl_cons, ih, pairedTopReduction_cons_apply]

/-- Every stored pivot is nonzero, and each later column is zero at all earlier
pivots. The pivot indices need not be numerically sorted. -/
def PairedEchelon {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) : Prop :=
  (∀ iw ∈ ds, iw.2.top iw.1 ≠ 0) ∧
    ds.Pairwise (fun iw jw => jw.2.top iw.1 = 0)

/-- An echelon table reduces all its stored upper columns to zero. -/
theorem pairedTopReduction_column_eq_zero {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) (h : PairedEchelon ds)
    (iw : Fin n × PairedColumn K n) (hiw : iw ∈ ds) :
    pairedTopReduction ds iw.2.top = 0 := by
  induction ds with
  | nil => simp at hiw
  | cons jw ds ih =>
    have hp := List.pairwise_cons.mp h.2
    have ht : PairedEchelon ds :=
      ⟨fun kw hkw => h.1 kw (List.mem_cons_of_mem _ hkw), hp.2⟩
    rcases List.mem_cons.mp hiw with heq | hiw
    · subst iw
      rw [pairedTopReduction_cons_apply, div_self (h.1 jw List.mem_cons_self)]
      simp
    · rw [pairedTopReduction_cons_apply, hp.1 iw hiw]
      simpa using ih ht hiw

/-- A vector in the span of the stored upper columns reduces to zero. -/
theorem reducePairedColumn_top_eq_zero_of_mem_span {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (hD : PairedEchelon D.toList)
    (v : PairedColumn K n)
    (hv : v.top ∈ Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top}) :
    (reducePairedColumn D v).top = 0 := by
  have hle : Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top} ≤
      LinearMap.ker (pairedTopReduction D.toList) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨iw, hiw, rfl⟩
    exact pairedTopReduction_column_eq_zero D.toList hD iw hiw
  rw [reducePairedColumn_top_eq_linear]
  exact hle hv

/-- Reduction changes the upper vector only by a combination of stored columns. -/
theorem reducePairedColumn_top_sub_mem {K : Type*} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top ∈ W) :
    v.top - (reducePairedColumn D v).top ∈ W := by
  rw [reducePairedColumn_top_eq_linear]
  generalize D.toList = ds at *
  induction ds generalizing v with
  | nil => simp [pairedTopReduction]
  | cons iw ds ih =>
    rw [pairedTopReduction_cons_apply]
    have h := ih {
      top := v.top - (v.top iw.1 / iw.2.top iw.1) • iw.2.top
      bottom := v.bottom - (v.top iw.1 / iw.2.top iw.1) • iw.2.bottom }
      (fun jw hjw => hD jw (List.mem_cons_of_mem _ hjw))
    have hc := W.smul_mem (v.top iw.1 / iw.2.top iw.1) (hD iw List.mem_cons_self)
    convert W.add_mem hc h using 1
    dsimp only
    abel

/-- The upper remainder is zero exactly for membership in the stored upper span. -/
theorem reducePairedColumn_top_eq_zero_iff {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (hD : PairedEchelon D.toList)
    (v : PairedColumn K n) :
    (reducePairedColumn D v).top = 0 ↔
      v.top ∈ Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top} := by
  constructor
  · intro hz
    have h := reducePairedColumn_top_sub_mem
      (Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top}) D v
      (fun iw hiw => Submodule.subset_span ⟨iw, hiw, rfl⟩)
    simpa [hz] using h
  · exact reducePairedColumn_top_eq_zero_of_mem_span D hD v

private theorem pivotScan_eq_find {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (r : PairedColumn K n)
    (is : List (Fin n)) :
    (Id.run do
      for i in is do
        if r.top i ≠ 0 then
          return D.push (i, r)
      return D) =
    match is.find? (fun i => r.top i ≠ 0) with
    | none => D
    | some i => D.push (i, r) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases hi : r.top i = 0
    · simpa [hi, List.forIn_cons] using ih
    · simp [hi, List.forIn_cons]

/-- The imperative pivot search selects the first nonzero upper coordinate. -/
theorem insertPairedColumn_eq_find {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    insertPairedColumn D v =
      match (List.finRange n).find? (fun i => (reducePairedColumn D v).top i ≠ 0) with
      | none => D
      | some i => D.push (i, reducePairedColumn D v) := by
  exact pivotScan_eq_find D (reducePairedColumn D v) (List.finRange n)

/-- Reduction leaves a coordinate unchanged when every upper column is zero there. -/
theorem pairedTopReduction_apply_of_zero {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) (i : Fin n)
    (h : ∀ jw ∈ ds, jw.2.top i = 0) (v : Fin n → K) :
    pairedTopReduction ds v i = v i := by
  induction ds generalizing v with
  | nil => rfl
  | cons jw ds ih =>
    rw [pairedTopReduction_cons_apply, ih (fun kw hkw => h kw (List.mem_cons_of_mem _ hkw))]
    simp [h jw List.mem_cons_self]

/-- Every old pivot coordinate vanishes in the reduced upper vector. -/
theorem pairedTopReduction_pivot_eq_zero {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) (h : PairedEchelon ds)
    (v : Fin n → K) (iw : Fin n × PairedColumn K n) (hiw : iw ∈ ds) :
    pairedTopReduction ds v iw.1 = 0 := by
  induction ds generalizing v with
  | nil => simp at hiw
  | cons jw ds ih =>
    have hp := List.pairwise_cons.mp h.2
    have ht : PairedEchelon ds :=
      ⟨fun kw hkw => h.1 kw (List.mem_cons_of_mem _ hkw), hp.2⟩
    rw [pairedTopReduction_cons_apply]
    rcases List.mem_cons.mp hiw with heq | hiw
    · subst iw
      rw [pairedTopReduction_apply_of_zero ds jw.1 hp.1]
      simp [div_mul_cancel₀ _ (h.1 jw List.mem_cons_self)]
    · exact ih ht _ hiw

/-- Adding a new pivot column preserves the triangular table invariant. -/
theorem insertPairedColumn_echelon {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (hD : PairedEchelon D.toList)
    (v : PairedColumn K n) : PairedEchelon (insertPairedColumn D v).toList := by
  rw [insertPairedColumn_eq_find]
  split
  · exact hD
  · rename_i i hi
    have hp : (reducePairedColumn D v).top i ≠ 0 := by
      simpa using List.find?_some hi
    simp only [Array.toList_push]
    refine ⟨?_, ?_⟩
    · intro jw hjw
      rcases List.mem_append.mp hjw with hjw | hjw
      · exact hD.1 jw hjw
      · have he : jw = (i, reducePairedColumn D v) := List.mem_singleton.mp hjw
        simpa [he] using hp
    · apply List.pairwise_append.mpr
      refine ⟨hD.2, List.pairwise_singleton _ _, ?_⟩
      intro jw hjw kw hkw
      have he : kw = (i, reducePairedColumn D v) := List.mem_singleton.mp hkw
      subst kw
      rw [reducePairedColumn_top_eq_linear]
      exact pairedTopReduction_pivot_eq_zero D.toList hD v.top jw hjw

/-- A vector already zero at every stored pivot is unchanged by reduction. -/
theorem pairedTopReduction_eq_self {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) (v : Fin n → K)
    (hv : ∀ iw ∈ ds, v iw.1 = 0) : pairedTopReduction ds v = v := by
  induction ds with
  | nil => rfl
  | cons iw ds ih =>
    rw [pairedTopReduction_cons_apply, hv iw List.mem_cons_self]
    simp only [zero_div, zero_smul, sub_zero]
    exact ih (fun jw hjw => hv jw (List.mem_cons_of_mem _ hjw))

/-- A nonzero upper remainder lies outside the span of the old upper columns. -/
theorem reducePairedColumn_top_not_mem_span {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (hD : PairedEchelon D.toList)
    (v : PairedColumn K n) (hne : (reducePairedColumn D v).top ≠ 0) :
    (reducePairedColumn D v).top ∉
      Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top} := by
  intro hm
  have hz := reducePairedColumn_top_eq_zero_of_mem_span D hD (reducePairedColumn D v) hm
  rw [reducePairedColumn_top_eq_linear, pairedTopReduction_eq_self] at hz
  · exact hne hz
  · intro iw hiw
    rw [reducePairedColumn_top_eq_linear]
    exact pairedTopReduction_pivot_eq_zero D.toList hD v.top iw hiw

/-- Insertion preserves the linear relation between the upper and lower blocks. -/
theorem insertPairedColumn_top_eq {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (F : Module.End K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = F iw.2.bottom)
    (hv : v.top = F v.bottom) :
    ∀ iw ∈ (insertPairedColumn D v).toList, iw.2.top = F iw.2.bottom := by
  rw [insertPairedColumn_eq_find]
  split
  · exact hD
  · rename_i i _
    intro iw hiw
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hiw
    rcases hiw with hiw | rfl
    · exact hD iw hiw
    · exact reducePairedColumn_top_eq F D v hD hv

/-- Insertion preserves membership of lower columns in a fixed subspace. -/
theorem insertPairedColumn_bottom_mem {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (W : Submodule K (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.bottom ∈ W) (hv : v.bottom ∈ W) :
    ∀ iw ∈ (insertPairedColumn D v).toList, iw.2.bottom ∈ W := by
  rw [insertPairedColumn_eq_find]
  split
  · exact hD
  · rename_i i _
    intro iw hiw
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hiw
    rcases hiw with hiw | rfl
    · exact hD iw hiw
    · exact reducePairedColumn_bottom_mem W D v hD hv

/-- Changing only lower columns leaves the echelon invariant unchanged. -/
theorem PairedEchelon.map_bottom {K : Type*} [Field K] {n : ℕ}
    (ds : List (Fin n × PairedColumn K n)) (h : PairedEchelon ds)
    (F : (Fin n → K) → (Fin n → K)) :
    PairedEchelon (ds.map (fun (i, w) => (i, ⟨w.top, F w.bottom⟩))) := by
  constructor
  · intro iw hiw
    obtain ⟨jw, hjw, rfl⟩ := List.mem_map.mp hiw
    exact h.1 jw hjw
  · exact List.pairwise_map.mpr h.2

/-- The subspace represented by the upper block of a paired table. -/
def pairedTopSpan {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) : Submodule K (Fin n → K) :=
  Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top}

/-- Appending a column adjoins precisely its upper vector to the upper span. -/
theorem pairedTopSpan_push {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (i : Fin n) (v : PairedColumn K n) :
    pairedTopSpan (D.push (i, v)) = pairedTopSpan D ⊔ Submodule.span K {v.top} := by
  unfold pairedTopSpan
  rw [← Submodule.span_union]
  congr 1
  ext w
  simp only [Array.toList_push, List.mem_append, List.mem_singleton,
    Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨iw, hiw, hw⟩
    rcases hiw with hiw | rfl
    · exact Or.inl ⟨iw, hiw, hw⟩
    · exact Or.inr hw
  · rintro (⟨iw, hiw, hw⟩ | hw)
    · exact ⟨iw, Or.inl hiw, hw⟩
    · exact ⟨(i, v), Or.inr rfl, hw⟩

private theorem sup_span_singleton_eq_of_sub_mem {K M : Type*} [Field K]
    [AddCommGroup M] [Module K M] (W : Submodule K M) (v r : M) (h : v-r ∈ W) :
    W ⊔ Submodule.span K {v} = W ⊔ Submodule.span K {r} := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    have ha : v-r ∈ W ⊔ Submodule.span K {r} := Submodule.mem_sup_left h
    have hb : r ∈ W ⊔ Submodule.span K {r} :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton r))
    simpa using Submodule.add_mem _ ha hb
  · apply sup_le le_sup_left
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    have ha : v-r ∈ W ⊔ Submodule.span K {v} := Submodule.mem_sup_left h
    have hb : v ∈ W ⊔ Submodule.span K {v} :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v))
    simpa using Submodule.sub_mem _ hb ha

/-- Column insertion preserves the represented span even if the column is discarded. -/
theorem pairedTopSpan_insertPairedColumn {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    pairedTopSpan (insertPairedColumn D v) =
      pairedTopSpan D ⊔ Submodule.span K {v.top} := by
  have hsub := reducePairedColumn_top_sub_mem (pairedTopSpan D) D v
    (fun iw hiw => Submodule.subset_span ⟨iw, hiw, rfl⟩)
  have heq := sup_span_singleton_eq_of_sub_mem (pairedTopSpan D) v.top
    (reducePairedColumn D v).top hsub
  rw [insertPairedColumn_eq_find]
  split
  · rename_i hn
    have hz : (reducePairedColumn D v).top = 0 := by
      funext i
      have hh := List.find?_eq_none.mp hn i (List.mem_finRange i)
      simpa using hh
    rw [heq, hz]
    simp
  · rw [pairedTopSpan_push, heq]

/-- Applying a map to lower columns leaves the represented upper span unchanged. -/
theorem pairedTopSpan_map_bottom {K : Type*} [Field K] {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (F : (Fin n → K) → (Fin n → K)) :
    pairedTopSpan (D.map (fun (i, w) => (i, ⟨w.top, F w.bottom⟩))) = pairedTopSpan D := by
  unfold pairedTopSpan
  congr 1
  ext w
  simp only [Array.toList_map, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨iw, ⟨jw, hjw, rfl⟩, hw⟩
    exact ⟨jw, hjw, hw⟩
  · rintro ⟨jw, hjw, hw⟩
    exact ⟨(jw.1, ⟨jw.2.top, F jw.2.bottom⟩), ⟨jw, hjw, rfl⟩, hw⟩

end SympyProofs.JordanKrylov
