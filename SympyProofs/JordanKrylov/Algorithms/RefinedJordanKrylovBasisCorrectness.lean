import SympyProofs.JordanKrylov.Algorithms.RefinedJordanKrylovBasisModel
import SympyProofs.JordanKrylov.Algorithms.ReduceKrylovGeneratorsCorrectness
import SympyProofs.JordanKrylov.Algorithms.PrimaryGeneratingCorrectness
import SympyProofs.JordanKrylov.Mathematics.RankSum

namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- The paired-column view of ordinary pending vectors, used only in proofs. -/
def terminalPairs {K : Type} {n : ℕ} (F : (Fin n → K) → (Fin n → K))
    (j : ℕ) (vs : List (Fin n → K)) : List (PairedColumn K n) :=
  vs.map (fun v => { top := F^[j - 1] v, bottom := v })

@[simp] theorem terminalPairs_nil {K : Type} {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (j : ℕ) : terminalPairs F j [] = [] := rfl

theorem terminalPairs_update {K : Type} {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (V : ℕ → List (Fin n → K))
    (j : ℕ) (vs : List (Fin n → K)) :
    (fun k => terminalPairs F k (Function.update V j vs k)) =
      Function.update (fun k => terminalPairs F k (V k)) j (terminalPairs F j vs) := by
  funext k
  by_cases hk : k = j
  · subst k; simp
  · simp [Function.update_of_ne hk]

/-- A nonzero upper remainder is a new generator, not an already accepted one. -/
theorem EliminationTableInvariant.remainder_not_mem
    (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : Set (Fin n → K)) (D : Array (Fin n × PairedColumn K n))
    (h : EliminationTableInvariant K A f ℓbar ℓ B D)
    (hp : 1 ≤ ℓ) (v : PairedColumn K n) (hv : ValidLayerColumn K A f ℓ v)
    (hn : (reducePairedColumn D v).top ≠ 0) :
    (reducePairedColumn D v).bottom ∉ B := by
  have hr := reducePairedColumn_rank_eq K A f hp D v h.paired hv.2 h.bounded hv.1 hn
  have he := reducePairedColumn_top_eq ((aeval A f)^(ℓ - 1)).mulVecLin D v h.paired hv.2
  have ht : (reducePairedColumn D v).top = terminalVector K A f (reducePairedColumn D v).bottom := by
    simpa only [terminalVector, hr, Matrix.mulVecLin_apply] using he
  intro hb
  apply reducePairedColumn_top_not_mem_span D h.echelon v hn
  change (reducePairedColumn D v).top ∈ pairedTopSpan D
  rw [h.terminal_span, ht]
  exact (le_iSup (fun b : B => krylovSpace K A (terminalVector K A f b.val)) ⟨_, hb⟩)
    (self_mem_krylovSpace K A _)

/-- The finite-set version of the rank-sum stopping theorem. -/
theorem independent_finset_stop
    (K : Subfield ℂ) [DecidableEq K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Finset (Fin n → K)) (hB : IsJordanKrylovIndependent K A (B : Set (Fin n → K)))
    (hk : (B : Set (Fin n → K)) ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (hs : (∑ v ∈ B, vectorRank K A f v) = multiplicity f A.charpoly) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) (B : Set (Fin n → K)) := by
  apply hB.isBasis_of_sum_ranks_eq K A f hf hm (B : Set (Fin n → K)) hk
  exact (Finset.sum_subtype B (fun _ => Iff.rfl) (vectorRank K A f)).symm.trans hs

/-- Preprocessing preserves bounds even when pending vectors have smaller rank than their bucket. -/
theorem reduceKrylovGenerators_bounded
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n : ℕ}
    (hops : Operations.IsCorrect K) (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓ : ℕ)
    (hV : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓ ∧ v ∈ powerKernel K A f j) :
    ∀ j v, v ∈ reduceKrylovGenerators (Operations.applyMatrix f A) V ℓ j →
      1 ≤ j ∧ j ≤ ℓ ∧ v ∈ powerKernel K A f j := by
  intro j v hv
  have hs := reduceKrylovGenerators_support K hops A f V ℓ
    (fun v hv => (hV ℓ v hv).2.2) (fun j v hv => ⟨(hV j v hv).1, (hV j v hv).2.1⟩) j v hv
  refine ⟨hs.1, hs.2, ?_⟩
  simp only [reduceKrylovGenerators, ← apply_ite, List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind] at hv
  change v ∈ ((reduceGeneratorColumns (V ℓ)).foldl (fun W v => if v ≠ 0 then
    Function.update W (boundedVectorRank (Operations.applyMatrix f A) v ℓ)
      (W (boundedVectorRank (Operations.applyMatrix f A) v ℓ) ++ [v]) else W)
    (Function.update V ℓ [])) j at hv
  rw [redistribute_mem] at hv
  rcases hv with hv | ⟨hv, hn, hr⟩
  · by_cases hj : j = ℓ
    · subst j; simp at hv
    · exact (hV j v (by simpa only [Function.update_of_ne hj] using hv)).2.2
  · have hk : v ∈ powerKernel K A f ℓ := by
      apply (Submodule.span_le.mpr (fun v hv => (hV ℓ v hv).2.2) :
        Submodule.span K {v | v ∈ V ℓ} ≤ _)
      rw [← reduceGeneratorColumns_span]
      exact Submodule.subset_span hv
    rw [boundedVectorRank_correct K hops A f v hn hk] at hr
    rw [← hr]
    exact mem_powerKernel_vectorRank K A f v hk

/-- Extracting the current bucket does not change the total remaining space. -/
theorem terminal_workSpace
    (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (F : (Fin n → K) → (Fin n → K)) (B : Set (Fin n → K))
    (V : ℕ → List (Fin n → K)) (ℓ : ℕ) :
    workSpace K A B (terminalPairs F ℓ (V ℓ))
      (fun j => terminalPairs F j (Function.update V ℓ [] j)) =
      generatorSpace K A B ⊔ generatorSpace K A {v | ∃ j, v ∈ V j} := by
  rw [terminalPairs_update, terminalPairs_nil]
  unfold workSpace
  rw [sup_assoc, ← pendingSpace_extract K A (fun j => terminalPairs F j (V j)) ℓ]
  congr 1
  simp only [pendingSpace, pairedListSpace, terminalPairs, List.mem_map,
    generatorSpace, Set.mem_ofPred_eq, iSup_exists, iSup_and]
  simp only [iSup_comm (ι := PairedColumn K n), iSup_comm (ι := Fin n → K)]
  simp

/-- Ordinary span preservation suffices for the remaining Krylov space. -/
theorem reduced_generatorSpace
    (K : Subfield ℂ) [DecidableEq K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (F : (Fin n → K) → (Fin n → K)) (V : ℕ → List (Fin n → K)) (ℓ : ℕ) :
    generatorSpace K A {v | ∃ j, v ∈ reduceKrylovGenerators F V ℓ j} =
      generatorSpace K A {v | ∃ j, v ∈ V j} := by
  apply generatorSpace_eq_of_span_eq
  have he (W : ℕ → List (Fin n → K)) :
      Submodule.span K {v | ∃ j, v ∈ W j} = layerSpan K W := by
    simp only [layerSpan, ← Submodule.span_iUnion]
    congr 1
    ext v
    simp
  rw [he, he]
  exact reduceKrylovGenerators_span K F V ℓ

/-- Procedure 4 preserves the work invariant at the start of a layer. -/
theorem EliminationWorkInvariant.preprocess
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n ℓbar ℓ : ℕ}
    (hops : Operations.IsCorrect K) (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (B : Set (Fin n → K))
    (D : Array (Fin n × PairedColumn K n)) (enabled : Bool) (limit : ℕ)
    (h : EliminationWorkInvariant K A f ℓbar ℓ B D
      (terminalPairs (Operations.applyMatrix f A) ℓ (V ℓ))
      (fun j => terminalPairs (Operations.applyMatrix f A) j (Function.update V ℓ [] j)))
    (hp : 1 ≤ ℓ) :
    let W := refinedPreprocess K A f enabled limit ℓ V
    EliminationWorkInvariant K A f ℓbar ℓ B D
      (terminalPairs (Operations.applyMatrix f A) ℓ (W ℓ))
      (fun j => terminalPairs (Operations.applyMatrix f A) j (Function.update W ℓ [] j)) := by
  dsimp only [refinedPreprocess]
  split
  · have hb : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓ ∧ v ∈ powerKernel K A f j := by
      intro j v hv
      by_cases hj : j = ℓ
      · subst j
        exact ⟨hp, le_rfl, (h.current _ (List.mem_map.mpr ⟨v, hv, rfl⟩)).1⟩
      · have hq := h.queued j ⟨(Operations.applyMatrix f A)^[j-1] v, v⟩
          (List.mem_map.mpr ⟨v, by simpa only [Function.update_of_ne hj] using hv, rfl⟩)
        exact ⟨hq.1, hq.2.1.le, hq.2.2.1⟩
    have ho := reduceKrylovGenerators_bounded K hops A f V ℓ hb
    refine ⟨h.table, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact ⟨(ho ℓ v hv).2.2, applyMatrix_iterate_eq_pow_mulVec K hops A f v (ℓ-1)⟩
    · intro j w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      have hj : j ≠ ℓ := by intro he; subst j; simp at hv
      rw [Function.update_of_ne hj] at hv
      have hh := ho j v hv
      exact ⟨hh.1, lt_of_le_of_ne hh.2.1 hj, hh.2.2,
        applyMatrix_iterate_eq_pow_mulVec K hops A f v (j-1)⟩
    · rw [terminal_workSpace, reduced_generatorSpace]
      simpa only [terminal_workSpace] using h.spans
  · exact h

/-- The recursive refinement maintains the elimination invariant and stops only
at a complete basis, either by exhaustion or by the rank-sum test. -/
theorem refinedElimination_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n ℓbar : ℕ}
    (hops : Operations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (m : ℕ) (hmult : m = multiplicity f A.charpoly) (preprocess : Bool) (limit : ℕ)
    (ℓ : ℕ) (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (B : ℕ → List (Fin n → K)) (used : ℕ) (D : Array (Fin n × PairedColumn K n))
    (hrB : BasisLayerRanks K A f B)
    (hp : 1 ≤ ℓ) (hle : ℓ ≤ ℓbar)
    (flat : Finset (Fin n → K)) (hflat : acceptedGenerators B = (flat : Set (Fin n → K)))
    (hs : used = ∑ v ∈ flat, vectorRank K A f v)
    (h : EliminationWorkInvariant K A f ℓbar ℓ (flat : Set (Fin n → K)) D
      (terminalPairs (Operations.applyMatrix f A) ℓ todo)
      (fun j => terminalPairs (Operations.applyMatrix f A) j (pending j))) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
      (acceptedGenerators (refinedElimination K A f m preprocess limit ℓ todo pending B used D)) ∧
      BasisLayerRanks K A f (refinedElimination K A f m preprocess limit ℓ todo pending B used D) := by
  induction ℓ generalizing todo pending B used D flat with
  | zero => omega
  | succ k outer =>
    induction todo generalizing pending B used D flat with
    | nil =>
      by_cases hk : k = 0
      · subst k
        simpa only [refinedElimination, Id.run, Nat.reduceAdd, ite_true, Pure.pure, hflat] using
          And.intro (h.finish K A f _ _ _) hrB
      · have hn := h.next_layer K hops A f (by omega) _ _ _
        have hn' : EliminationWorkInvariant K A f ℓbar k (flat : Set (Fin n → K))
            (D.map (fun (i,w) => (i, ⟨w.top, Operations.applyMatrix f A w.bottom⟩)))
            (terminalPairs (Operations.applyMatrix f A) k (pending k))
            (fun j => terminalPairs (Operations.applyMatrix f A) j (Function.update pending k [] j)) := by
          simpa only [terminalPairs_update, terminalPairs_nil] using hn
        have hp := hn'.preprocess K hops A f pending (flat : Set (Fin n → K)) _ preprocess limit (by omega)
        have hr := outer ((refinedPreprocess K A f preprocess limit k pending) k)
          (Function.update (refinedPreprocess K A f preprocess limit k pending) k []) B used
          (D.map (fun (i,w) => (i, ⟨w.top, Operations.applyMatrix f A w.bottom⟩)))
          hrB (by omega) (by omega) flat hflat hs
          hp
        simpa only [refinedElimination, Id.run, hk, ite_false, Pure.pure] using hr
    | cons v todo inner =>
      let pair : PairedColumn K n := ⟨(Operations.applyMatrix f A)^[k] v, v⟩
      let r := reducePairedColumn D pair
      have hh : EliminationWorkInvariant K A f ℓbar (k+1) (flat : Set (Fin n → K)) D
          (pair :: terminalPairs (Operations.applyMatrix f A) (k+1) todo)
          (fun j => terminalPairs (Operations.applyMatrix f A) j (pending j)) := by
        simpa only [terminalPairs, List.map_cons, Nat.add_sub_cancel] using h
      have hv := hh.current pair (List.mem_cons_self ..)
      rw [refinedElimination_cons]
      dsimp only
      by_cases ht : r.top ≠ 0
      · rw [ite_eq_left ht]
        have ha := hh.accept K A f hf hm _ D pair _ _ hp hle ht
        have hrank : vectorRank K A f r.bottom = k+1 :=
          reducePairedColumn_rank_eq K A f hp D pair hh.table.paired hv.2 hh.table.bounded hv.1 ht
        have hnew : r.bottom ∉ flat := hh.table.remainder_not_mem K A f _ D hp pair hv ht
        have hsum : used + (k+1) = ∑ w ∈ insert r.bottom flat, vectorRank K A f w := by
          rw [Finset.sum_insert hnew, hrank, ← hs, Nat.add_comm]
        have hflat' : acceptedGenerators (Function.update B (k+1) (r.bottom :: (B (k+1)))) =
            (insert r.bottom flat : Finset (Fin n → K)) := by
          rw [acceptedGenerators_cons, hflat, Finset.coe_insert]
        have hrB' := hrB.cons K A f B (k+1) r.bottom (by omega) hrank
        by_cases hstop : used + (k+1) = m
        · rw [ite_eq_left hstop]
          refine ⟨?_, hrB'⟩
          rw [hflat']
          apply independent_finset_stop K A f hf hm _
            (by simpa only [Finset.coe_insert] using ha.table.independent)
            (by simpa only [Finset.coe_insert] using ha.table.primary)
          exact hsum.symm.trans (hstop.trans hmult)
        · rw [ite_eq_right hstop]
          exact inner pending (Function.update B (k+1) (r.bottom :: (B (k+1)))) (used+(k+1)) _ hrB'
            (insert r.bottom flat) hflat' hsum
            (by simpa only [Finset.coe_insert] using ha)
      · rw [ite_eq_right ht]
        have hz : r.top = 0 := not_ne_iff.mp ht
        by_cases hb : r.bottom ≠ 0 ∧ 1 < k+1
        · rw [ite_eq_left hb]
          have hk : r.bottom ∈ powerKernel K A f k := by
            simpa only [Nat.add_sub_cancel] using
              reducePairedColumn_mem_previous_powerKernel K A f D pair hh.table.paired hv.2 hz
          rw [boundedVectorRank_correct K hops A f r.bottom hb.1 hk]
          apply inner _ B used D hrB flat hflat hs
          have hq := hh.requeue K A f _ D pair _ _ hz hb.1
          change EliminationWorkInvariant K A f ℓbar (k+1) (flat : Set (Fin n → K)) D
            (terminalPairs (Operations.applyMatrix f A) (k+1) todo)
            (fun j => terminalPairs (Operations.applyMatrix f A) j
              (Function.update pending (vectorRank K A f r.bottom)
                (pending (vectorRank K A f r.bottom) ++ [r.bottom]) j))
          rw [terminalPairs_update]
          simpa only [terminalPairs, List.map_append, List.map_cons, List.map_nil,
            applyMatrix_iterate_eq_pow_mulVec K hops A f, terminalVector] using hq
        · rw [ite_eq_right hb]
          have hbzero : r.bottom = 0 := by
            by_contra hn
            have hkle : ¬ 1 < k+1 := fun hlt => hb ⟨hn, hlt⟩
            have hk : k = 0 := by omega
            subst k
            exact hn (reducePairedColumn_bottom_eq_zero_at_rank_one K D pair
              (by simpa using hh.table.paired) (by simpa using hv.2) hz)
          exact inner pending B used D hrB flat hflat hs (hh.discard K A f _ D pair _ _ hbzero)

/-- The ordinary rank buckets establish the paired work invariant. -/
theorem refined_initial_invariant
    (K : Subfield ℂ) [Operations K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (hops : Operations.IsCorrect K)
    (hgen : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar) (algorithmInputSet V ℓbar))
    (hr : RankedLayers K A f V)
    (hs : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓbar) :
    EliminationWorkInvariant K A f ℓbar ℓbar (∅ : Set (Fin n → K)) #[]
      (terminalPairs (Operations.applyMatrix f A) ℓbar (V ℓbar))
      (fun j => terminalPairs (Operations.applyMatrix f A) j
        (Function.update V ℓbar [] j)) := by
  have he : initialPending (Operations.applyMatrix f A) V ℓbar =
      fun j => terminalPairs (Operations.applyMatrix f A) j (V j) := by
    funext j
    by_cases hj : 1 ≤ j ∧ j ≤ ℓbar
    · simp [initialPending, hj, terminalPairs]
    · have hz : V j = [] := List.eq_nil_iff_forall_not_mem.mpr fun v hv => hj (hs j v hv)
      simp [initialPending, hj, hz]
  have h := initial_workInvariant K A f V hops hgen
    (fun j _ _ v hv => (hr j v hv).2.1)
  dsimp only at h
  rw [he] at h
  simpa only [terminalPairs_update, terminalPairs_nil, acceptedGenerators,
    List.not_mem_nil, exists_false, Set.ofPred_false] using h

/-- Selecting the initial generator directly agrees with elimination against an empty table. -/
theorem refined_initialization_eq
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n : ℕ}
    (hops : Operations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (W : ℕ → List (Fin n → K)) (ℓbar m : ℕ) (preprocess : Bool) (hr : RankedLayers K A f W) :
    (let run := fun W B used D => refinedElimination K A f m preprocess ℓbar ℓbar
        (W ℓbar) (Function.update W ℓbar []) B used D
      match W ℓbar with
      | [] => run W (fun _ => []) 0 #[]
      | v :: rest =>
        if ℓbar = m then Function.update (fun _ => []) ℓbar [v] else
          let D := ((List.range f.natDegree).foldl
            (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
              (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩))
            (#[], ⟨(Operations.applyMatrix f A)^[ℓbar - 1] v, v⟩)).1
          run (Function.update W ℓbar rest) (Function.update (fun _ => []) ℓbar [v]) ℓbar D) =
      refinedElimination K A f m preprocess ℓbar ℓbar (W ℓbar) (Function.update W ℓbar []) (fun _ => []) 0 #[] := by
  cases hw : W ℓbar with
  | nil => simp only [hw]
  | cons v rest =>
    have hv := hr ℓbar v (by rw [hw]; exact List.mem_cons_self)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓbar ≠ 0)
    have hn : v ≠ 0 := by
      intro hz
      simp [hz, vectorRank_zero] at hv
    have ht := applyMatrix_iterate_ne_zero_of_lt_vectorRank K hops A f v hn
      (show k < vectorRank K A f v by omega)
    rw [refinedElimination_cons]
    simp [reducePairedColumn, ht, Function.update_idem]

/-- The output generates a Jordan–Krylov basis and retains exact positive rank layers. -/
theorem computeRefinedJordanKrylovBasis_correct_of_generating
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n ℓbar m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (preprocess : Bool)
    (hops : Operations.IsCorrect K)
    (hf : Irreducible f) (hm : f.Monic)
    (hmultiplicity : m = multiplicity f A.charpoly)
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
      (acceptedGenerators (computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess)) ∧
      BasisLayerRanks K A f (computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess) := by
  rw [computeRefinedJordanKrylovBasis_eq_model K A f V ℓbar m preprocess hf.natDegree_pos]
  let U := fun j => if 1 ≤ j ∧ j ≤ ℓbar then V j else []
  have hu : algorithmInputSet U ℓbar = algorithmInputSet V ℓbar := by
    ext v
    simp only [algorithmInputSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hp, hl, hv⟩
      exact ⟨j, hp, hl, by simpa only [U, hp, hl, and_self, ite_true] using hv⟩
    · rintro ⟨j, hp, hl, hv⟩
      exact ⟨j, hp, hl, by simpa only [U, hp, hl, and_self, ite_true] using hv⟩
  have hus : ∀ j v, v ∈ U j → 1 ≤ j ∧ j ≤ ℓbar := by
    intro j v hv
    dsimp only [U] at hv
    split at hv
    · assumption
    · simp at hv
  have hur : RankedLayers K A f U := by
    intro j v hv
    have hj := hus j v hv
    have hv' : v ∈ V j := by simpa only [U, hj.1, hj.2, and_self, ite_true] using hv
    have hr := hranks j hj.1 hj.2 v hv'
    have hk := algorithmInput_mem_powerKernel K A f V hgenerating hj.1 hj.2 hv'
    exact ⟨hj.1, hr, by simpa only [hr] using mem_powerKernel_vectorRank K A f v hk⟩
  have hug : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar) (algorithmInputSet U ℓbar) := by
    rw [hu]; exact hgenerating
  have finish (W : ℕ → List (Fin n → K))
      (hg : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar) (algorithmInputSet W ℓbar))
      (hr : RankedLayers K A f W) (hs : ∀ j v, v ∈ W j → 1 ≤ j ∧ j ≤ ℓbar) :
      IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
        (acceptedGenerators (refinedElimination K A f m preprocess ℓbar ℓbar (W ℓbar) (Function.update W ℓbar []) (fun _ => []) 0 #[])) ∧
      BasisLayerRanks K A f
        (refinedElimination K A f m preprocess ℓbar ℓbar (W ℓbar) (Function.update W ℓbar []) (fun _ => []) 0 #[]) := by
    by_cases hz : ℓbar = 0
    · subst ℓbar
      simp only [refinedElimination, Id.run, Pure.pure, acceptedGenerators_empty, powerKernel_zero, basisLayerRanks_empty, and_true]
      exact ⟨empty_isKrylovGeneratingSet_bot K A, isJordanKrylovIndependent_empty K A⟩
    exact refinedElimination_correct K hops A f hf hm m hmultiplicity preprocess ℓbar ℓbar _ _ (fun _ => []) 0 #[]
      (basisLayerRanks_empty K A f) (by omega) le_rfl ∅ (by simp) (by simp) (by simpa only [Finset.coe_empty] using refined_initial_invariant K A f W hops hg hr hs)
  cases preprocess with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h := finish U hug hur hus
    rw [← refined_initialization_eq K hops A f U ℓbar m false hur] at h
    cases hw : U ℓbar <;> dsimp only [U] at hw h ⊢ <;> simpa only [hw] using h
  | true =>
    have hc := reduceKrylovGenerators_correct K hops A f U ℓbar _ hug hur hus
    simp only [↓reduceIte]
    have h := finish _ hc.1 hc.2
      (reduceKrylovGenerators_support K hops A f U ℓbar (fun v hv => (hur ℓbar v hv).2.2) hus)
    rw [← refined_initialization_eq K hops A f _ ℓbar m true hc.2] at h
    cases hw : reduceKrylovGenerators (Operations.applyMatrix f A) U ℓbar ℓbar <;>
      dsimp only [U] at hw h ⊢ <;> simpa only [hw] using h

/-- Algorithms 1 and 3 produce a Jordan–Krylov basis from a spanning family
and its minimal annihilating polynomials, with or without preprocessing. -/
theorem computeRefinedJordanKrylovBasis_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin s → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin s → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (preprocess : Bool) (hops : Operations.IsCorrect K) :
    IsJordanKrylovBasis K A (powerKernel K A f (multiplicity f (minpoly K A)))
      (acceptedGenerators (computeRefinedJordanKrylovBasis K A f (computePrimaryGenerators K A e f p)
        (multiplicity f (minpoly K A)) (multiplicity f A.charpoly) preprocess)) := by
  refine (computeRefinedJordanKrylovBasis_correct_of_generating K A f
    (computePrimaryGenerators K A e f p) preprocess hops hf hm rfl ?_ ?_).1
  · rw [computePrimaryGenerators_inputSet_eq K hops A e f hf hm p
      (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)
      (fun i => by
        rw [multiplicity_minpoly_eq_max_spanning K A e he f hf hm, hp i]
        exact Finset.le_sup (f := fun j => multiplicity f
          (minimalAnnihilatingPolynomial K A (e j))) (Finset.mem_univ i))]
    exact computePrimaryGenerators_correct K hops A e he f hf hm p hp
  · intro ℓ _ _ v hv
    exact computePrimaryGenerators_ranks K hops A e f hf hm p hp ℓ v hv

/-- Algorithms 1 and 3 return generators in their exact positive rank layers. -/
theorem computeRefinedJordanKrylovBasis_ranks
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin s → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin s → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (preprocess : Bool) (hops : Operations.IsCorrect K) :
    BasisLayerRanks K A f (computeRefinedJordanKrylovBasis K A f (computePrimaryGenerators K A e f p)
        (multiplicity f (minpoly K A)) (multiplicity f A.charpoly) preprocess) := by
  refine (computeRefinedJordanKrylovBasis_correct_of_generating K A f
    (computePrimaryGenerators K A e f p) preprocess hops hf hm rfl ?_ ?_).2
  · rw [computePrimaryGenerators_inputSet_eq K hops A e f hf hm p
      (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)
      (fun i => by
        rw [multiplicity_minpoly_eq_max_spanning K A e he f hf hm, hp i]
        exact Finset.le_sup (f := fun j => multiplicity f
          (minimalAnnihilatingPolynomial K A (e j))) (Finset.mem_univ i))]
    exact computePrimaryGenerators_correct K hops A e he f hf hm p hp
  · intro ℓ _ _ v hv
    exact computePrimaryGenerators_ranks K hops A e f hf hm p hp ℓ v hv

end SympyProofs.JordanKrylov
