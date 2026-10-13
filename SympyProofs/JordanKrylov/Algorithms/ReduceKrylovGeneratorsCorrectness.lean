import SympyProofs.JordanKrylov.Algorithms.ReduceKrylovGenerators
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisOuter

namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- The bounded search computes the exact rank for a nonzero bounded vector. -/
theorem boundedVectorRank_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n k : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Fin n → K)
    (hv : v ≠ 0) (hk : v ∈ powerKernel K A f k) :
    boundedVectorRank (PolynomialOperations.applyMatrix f A) v k = vectorRank K A f v := by
  let F := PolynomialOperations.applyMatrix f A
  have hscan := residualRankSearch_correct K hops A f v hv hk
  have hproject := List.foldl_hom
    (fun s : ℕ × (Fin n → K) × (Fin n → K) => (s.1, s.2.2))
    (g₁ := fun s j => if s.1 = 0 then
      if F s.2.2 = 0 then (j + 1, s.2.2, s.2.2) else (s.1, s.2.1, F s.2.2)
      else s)
    (g₂ := fun s j => if s.1 = 0 then
      if F s.2 = 0 then (j + 1, s.2) else (s.1, F s.2)
      else s)
    (l := List.range k) (init := (0, v, v)) (by
      intro s j
      split <;> simp_all only
      split <;> rfl)
  simp only [Id.run, ← apply_ite, List.forIn_pure_yield_eq_foldl, pure_bind] at hscan
  simp only [boundedVectorRank, Id.run, ← apply_ite, List.forIn_pure_yield_eq_foldl, pure_bind]
  change ((List.range k).foldl _ (0, v)).1 = _
  rw [hproject]
  exact congrArg Prod.fst hscan

/-- Ordinary column reduction preserves the linear span. -/
theorem reduceGeneratorColumns_span {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (vs : List (Fin n → K)) :
    Submodule.span K {v | v ∈ reduceGeneratorColumns vs} = Submodule.span K {v | v ∈ vs} := by
  have h (xs : List (Fin n → K)) (D : Array (Fin n × PairedColumn K n)) :
      pairedTopSpan (xs.foldl (fun D v => insertPairedColumn D ⟨v, v⟩) D) =
        pairedTopSpan D ⊔ Submodule.span K {v | v ∈ xs} := by
    induction xs generalizing D with
    | nil => simp
    | cons v vs ih =>
      rw [List.foldl_cons, ih, pairedTopSpan_insertPairedColumn]
      have he : {x | x ∈ v :: vs} = insert v {x | x ∈ vs} := by ext; simp
      rw [he, Submodule.span_insert]
      exact sup_assoc _ _ _
  have he (D : Array (Fin n × PairedColumn K n)) :
      Submodule.span K {v | v ∈ D.toList.map (fun iw => iw.2.top)} = pairedTopSpan D := by
    congr 1
    ext v
    simp only [List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨iw, hiw, rfl⟩; exact ⟨iw, hiw, rfl⟩
    · rintro ⟨iw, hiw, rfl⟩; exact ⟨iw, hiw, rfl⟩
  simp only [reduceGeneratorColumns, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  change Submodule.span K {v | v ∈ (vs.foldl
    (fun D v => insertPairedColumn D ⟨v, v⟩) #[]).toList.map (fun iw => iw.2.top)} = _
  rw [he, h]
  simp [pairedTopSpan]

/-- The ordinary span of all rank buckets. -/
noncomputable def layerSpan (K : Subfield ℂ) {n : ℕ}
    (V : ℕ → List (Fin n → K)) : Submodule K (Fin n → K) :=
  ⨆ j, Submodule.span K {v | v ∈ V j}

theorem layerSpan_extract (K : Subfield ℂ) {n : ℕ}
    (V : ℕ → List (Fin n → K)) (j : ℕ) :
    layerSpan K V = layerSpan K (Function.update V j []) ⊔
      Submodule.span K {v | v ∈ V j} := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases he : k = j
    · subst k; exact le_sup_right
    · exact (show Submodule.span K {v | v ∈ V k} ≤
        layerSpan K (Function.update V j []) by
        simpa only [layerSpan, Function.update_of_ne he] using
          (le_iSup (fun k => Submodule.span K {v | v ∈ Function.update V j [] k}) k)).trans
        le_sup_left
  · refine sup_le (iSup_le fun k => ?_) (le_iSup (fun k => Submodule.span K {v | v ∈ V k}) j)
    by_cases he : k = j
    · subst k; simp
    · simpa only [Function.update_of_ne he, layerSpan] using
        (le_iSup (fun k => Submodule.span K {v | v ∈ V k}) k)

theorem layerSpan_append (K : Subfield ℂ) {n : ℕ}
    (V : ℕ → List (Fin n → K)) (j : ℕ) (v : Fin n → K) :
    layerSpan K (Function.update V j (V j ++ [v])) =
      layerSpan K V ⊔ Submodule.span K {v} := by
  rw [layerSpan_extract K _ j, layerSpan_extract K V j]
  simp only [Function.update_self, Function.update_idem]
  have he : {x | x ∈ V j ++ [v]} = {x | x ∈ V j} ∪ {v} := by ext; simp [or_comm]
  rw [he, Submodule.span_union, sup_assoc]

/-- Reindexing nonzero reduced columns preserves the span, regardless of the rank oracle. -/
theorem redistribute_span (K : Subfield ℂ) [DecidableEq K] {n : ℕ}
    (rank : (Fin n → K) → ℕ) (vs : List (Fin n → K))
    (V : ℕ → List (Fin n → K)) :
    layerSpan K (vs.foldl (fun V v => if v ≠ 0 then
      Function.update V (rank v) (V (rank v) ++ [v]) else V) V) =
      layerSpan K V ⊔ Submodule.span K {v | v ∈ vs} := by
  induction vs generalizing V with
  | nil => simp
  | cons v vs ih =>
    rw [List.foldl_cons, ih]
    have he : {x | x ∈ v :: vs} = insert v {x | x ∈ vs} := by ext; simp
    rw [he, Submodule.span_insert]
    by_cases hv : v = 0
    · simp [hv]
    · rw [ite_eq_left hv, layerSpan_append, sup_assoc]

/-- Procedure 4 preserves the ordinary span of the entire family. -/
theorem reduceKrylovGenerators_span (K : Subfield ℂ) [DecidableEq K] {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (V : ℕ → List (Fin n → K)) (ℓ : ℕ) :
    layerSpan K (reduceKrylovGenerators F V ℓ) = layerSpan K V := by
  simp only [reduceKrylovGenerators, ← apply_ite, List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind]
  change layerSpan K ((reduceGeneratorColumns (V ℓ)).foldl _ _) = _
  rw [redistribute_span, reduceGeneratorColumns_span, ← layerSpan_extract]

/-- Buckets carry their exact positive rank and a corresponding kernel bound. -/
def RankedLayers (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (V : ℕ → List (Fin n → K)) : Prop :=
  ∀ j v, v ∈ V j → 1 ≤ j ∧ vectorRank K A f v = j ∧ v ∈ powerKernel K A f j

/-- Reduction and reindexing preserve the rank contract. -/
theorem reduceKrylovGenerators_ranked
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K)) (ℓ : ℕ)
    (hV : RankedLayers K A f V) :
    RankedLayers K A f (reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) V ℓ) := by
  have hker : ∀ v ∈ reduceGeneratorColumns (V ℓ), v ∈ powerKernel K A f ℓ := by
    intro v hv
    have hs : Submodule.span K {v | v ∈ V ℓ} ≤ powerKernel K A f ℓ :=
      Submodule.span_le.mpr fun v hv => (hV ℓ v hv).2.2
    rw [← reduceGeneratorColumns_span] at hs
    exact hs (Submodule.subset_span hv)
  have hinit : RankedLayers K A f (Function.update V ℓ []) := by
    intro j v hv
    by_cases hj : j = ℓ
    · subst j; simp at hv
    · exact hV j v (by simpa only [Function.update_of_ne hj] using hv)
  have hfold (vs : List (Fin n → K)) (W : ℕ → List (Fin n → K))
      (hw : RankedLayers K A f W) (hk : ∀ v ∈ vs, v ∈ powerKernel K A f ℓ) :
      RankedLayers K A f (vs.foldl (fun W v => if v ≠ 0 then
        Function.update W (boundedVectorRank (PolynomialOperations.applyMatrix f A) v ℓ)
          (W (boundedVectorRank (PolynomialOperations.applyMatrix f A) v ℓ) ++ [v]) else W) W) := by
    induction vs generalizing W with
    | nil => exact hw
    | cons v vs ih =>
      apply ih _ _ (fun w h => hk w (List.mem_cons_of_mem _ h))
      by_cases hv : v = 0
      · simpa [hv] using hw
      · dsimp only
        rw [ite_eq_left hv, boundedVectorRank_correct K hops A f v hv (hk v (by simp))]
        intro j w hmem
        by_cases hj : j = vectorRank K A f v
        · subst j
          simp only [Function.update_self, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | rfl
          · exact hw _ _ hmem
          · exact ⟨(vectorRank_bounds K A f w hv (hk w (by simp))).1, rfl,
              mem_powerKernel_vectorRank K A f w (hk w (by simp))⟩
        · exact hw _ _ (by simpa only [Function.update_of_ne hj] using hmem)
  simp only [reduceKrylovGenerators, ← apply_ite, List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind]
  exact hfold _ _ hinit hker

theorem redistribute_mem {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (rank : (Fin n → K) → ℕ) (vs : List (Fin n → K))
    (V : ℕ → List (Fin n → K)) (j : ℕ) (x : Fin n → K) :
    x ∈ (vs.foldl (fun V v => if v ≠ 0 then
      Function.update V (rank v) (V (rank v) ++ [v]) else V) V) j ↔
      x ∈ V j ∨ (x ∈ vs ∧ x ≠ 0 ∧ rank x = j) := by
  induction vs generalizing V with
  | nil => simp
  | cons v vs ih =>
    rw [List.foldl_cons, ih]
    by_cases hv : v = 0
    · simp [hv]
      aesop
    · by_cases hj : j = rank v
      · subst j; simp [hv]; aesop
      · simp [hv, Function.update_of_ne hj]; aesop

/-- Reduction never introduces a layer above its input bound. -/
theorem reduceKrylovGenerators_support
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K)) (ℓ : ℕ)
    (hker : ∀ v ∈ V ℓ, v ∈ powerKernel K A f ℓ)
    (hs : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓ) :
    ∀ j v, v ∈ reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) V ℓ j →
      1 ≤ j ∧ j ≤ ℓ := by
  intro j v hv
  simp only [reduceKrylovGenerators, ← apply_ite, List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind] at hv
  change v ∈ ((reduceGeneratorColumns (V ℓ)).foldl (fun W v => if v ≠ 0 then
    Function.update W (boundedVectorRank (PolynomialOperations.applyMatrix f A) v ℓ)
      (W (boundedVectorRank (PolynomialOperations.applyMatrix f A) v ℓ) ++ [v]) else W)
    (Function.update V ℓ [])) j at hv
  rw [redistribute_mem] at hv
  rcases hv with hv | ⟨hv, hn, hr⟩
  · by_cases hj : j = ℓ
    · subst j; simp at hv
    · exact hs j v (by simpa only [Function.update_of_ne hj] using hv)
  · have hk : v ∈ powerKernel K A f ℓ := by
      apply (Submodule.span_le.mpr hker : Submodule.span K {v | v ∈ V ℓ} ≤ _)
      rw [← reduceGeneratorColumns_span]
      exact Submodule.subset_span hv
    rw [boundedVectorRank_correct K hops A f v hn hk] at hr
    simpa only [hr] using vectorRank_bounds K A f v hn hk

/-- Equal ordinary spans give equal Krylov-generated spaces. -/
theorem generatorSpace_eq_of_span_eq (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (S T : Set (Fin n → K))
    (h : Submodule.span K S = Submodule.span K T) :
    generatorSpace K A S = generatorSpace K A T := by
  have hle (S T : Set (Fin n → K)) (hst : Submodule.span K S ≤ Submodule.span K T) :
      generatorSpace K A S ≤ generatorSpace K A T := by
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    apply krylovSpace_le K A v (generatorSpace K A T)
    · apply (Submodule.span_le.mpr (fun w hw =>
        (le_iSup_of_le w (le_iSup_of_le hw le_rfl) : krylovSpace K A w ≤ generatorSpace K A T)
          (self_mem_krylovSpace K A w)))
      exact hst (Submodule.subset_span hv)
    · exact generatorSpace_stable K A T
  exact le_antisymm (hle S T h.le) (hle T S h.ge)

theorem layerSpan_eq_span_input (K : Subfield ℂ) {n : ℕ}
    (V : ℕ → List (Fin n → K)) (ℓ : ℕ)
    (hs : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓ) :
    layerSpan K V = Submodule.span K (algorithmInputSet V ℓ) := by
  apply le_antisymm
  · apply iSup_le
    intro j
    apply Submodule.span_mono
    intro v hv
    exact ⟨j, (hs j v hv).1, (hs j v hv).2, hv⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨j, _, _, hv⟩
    exact (le_iSup (fun j => Submodule.span K {v | v ∈ V j}) j) (Submodule.subset_span hv)

/-- Procedure 4 preserves Krylov generation and the exact rank layers. -/
theorem reduceKrylovGenerators_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K)) (ℓ : ℕ)
    (W : Submodule K (Fin n → K))
    (hgen : IsKrylovGeneratingSet K A W (algorithmInputSet V ℓ))
    (hr : RankedLayers K A f V)
    (hs : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓ) :
    let out := reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) V ℓ
    IsKrylovGeneratingSet K A W (algorithmInputSet out ℓ) ∧ RankedLayers K A f out := by
  dsimp only
  refine ⟨?_, reduceKrylovGenerators_ranked K hops A f V ℓ hr⟩
  have ho := reduceKrylovGenerators_support K hops A f V ℓ (fun v hv => (hr ℓ v hv).2.2) hs
  have he := reduceKrylovGenerators_span K (PolynomialOperations.applyMatrix f A) V ℓ
  rw [layerSpan_eq_span_input K _ ℓ ho, layerSpan_eq_span_input K V ℓ hs] at he
  exact hgen.trans (generatorSpace_eq_of_span_eq K A _ _ he).symm

end SympyProofs.JordanKrylov
