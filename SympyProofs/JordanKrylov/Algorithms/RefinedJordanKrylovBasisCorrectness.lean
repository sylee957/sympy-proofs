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

/-- The recursive refinement maintains the elimination invariant and stops only
at a complete basis, either by exhaustion or by the rank-sum test. -/
theorem refinedElimination_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n ℓbar : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (m : ℕ) (hmult : m = multiplicity f A.charpoly)
    (ℓ : ℕ) (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (B : Finset (Fin n → K)) (used : ℕ) (D : Array (Fin n × PairedColumn K n))
    (hp : 1 ≤ ℓ) (hle : ℓ ≤ ℓbar)
    (hs : used = ∑ v ∈ B, vectorRank K A f v)
    (h : EliminationWorkInvariant K A f ℓbar ℓ (B : Set (Fin n → K)) D
      (terminalPairs (PolynomialOperations.applyMatrix f A) ℓ todo)
      (fun j => terminalPairs (PolynomialOperations.applyMatrix f A) j (pending j))) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
      (refinedElimination K A f m ℓ todo pending B used D : Set (Fin n → K)) := by
  induction ℓ generalizing todo pending B used D with
  | zero => omega
  | succ k outer =>
    induction todo generalizing pending B used D with
    | nil =>
      by_cases hk : k = 0
      · subst k
        simpa only [refinedElimination, Id.run, Nat.reduceAdd, ite_true, Pure.pure] using
          h.finish K A f _ _ _
      · have hn := h.next_layer K hops A f (by omega) _ _ _
        have hr := outer (pending k) (Function.update pending k []) B used
          (D.map (fun (i,w) => (i, ⟨w.top, PolynomialOperations.applyMatrix f A w.bottom⟩)))
          (by omega) (by omega) hs
          (by simpa only [terminalPairs_update, terminalPairs_nil] using hn)
        simpa only [refinedElimination, Id.run, hk, ite_false, Pure.pure] using hr
    | cons v todo inner =>
      let pair : PairedColumn K n := ⟨(PolynomialOperations.applyMatrix f A)^[k] v, v⟩
      let r := reducePairedColumn D pair
      have hh : EliminationWorkInvariant K A f ℓbar (k+1) (B : Set (Fin n → K)) D
          (pair :: terminalPairs (PolynomialOperations.applyMatrix f A) (k+1) todo)
          (fun j => terminalPairs (PolynomialOperations.applyMatrix f A) j (pending j)) := by
        simpa only [terminalPairs, List.map_cons, Nat.add_sub_cancel] using h
      have hv := hh.current pair (List.mem_cons_self ..)
      rw [refinedElimination_cons]
      dsimp only
      by_cases ht : r.top ≠ 0
      · rw [ite_eq_left ht]
        have ha := hh.accept K A f hf hm _ D pair _ _ hp hle ht
        have hrank : vectorRank K A f r.bottom = k+1 :=
          reducePairedColumn_rank_eq K A f hp D pair hh.table.paired hv.2 hh.table.bounded hv.1 ht
        have hnew : r.bottom ∉ B := hh.table.remainder_not_mem K A f _ D hp pair hv ht
        have hsum : used + (k+1) = ∑ w ∈ insert r.bottom B, vectorRank K A f w := by
          rw [Finset.sum_insert hnew, hrank, ← hs, Nat.add_comm]
        by_cases hstop : used + (k+1) = m
        · rw [ite_eq_left hstop]
          apply independent_finset_stop K A f hf hm _
            (by simpa only [Finset.coe_insert] using ha.table.independent)
            (by simpa only [Finset.coe_insert] using ha.table.primary)
          exact hsum.symm.trans (hstop.trans hmult)
        · rw [ite_eq_right hstop]
          exact inner pending (insert r.bottom B) (used+(k+1)) _ hsum
            (by simpa only [Finset.coe_insert] using ha)
      · rw [ite_eq_right ht]
        have hz : r.top = 0 := not_ne_iff.mp ht
        by_cases hb : r.bottom ≠ 0 ∧ 1 < k+1
        · rw [ite_eq_left hb]
          have hk : r.bottom ∈ powerKernel K A f k := by
            simpa only [Nat.add_sub_cancel] using
              reducePairedColumn_mem_previous_powerKernel K A f D pair hh.table.paired hv.2 hz
          rw [boundedVectorRank_correct K hops A f r.bottom hb.1 hk]
          apply inner _ B used D hs
          have hq := hh.requeue K A f _ D pair _ _ hz hb.1
          change EliminationWorkInvariant K A f ℓbar (k+1) (B : Set (Fin n → K)) D
            (terminalPairs (PolynomialOperations.applyMatrix f A) (k+1) todo)
            (fun j => terminalPairs (PolynomialOperations.applyMatrix f A) j
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
          exact inner pending B used D hs (hh.discard K A f _ D pair _ _ hbzero)

/-- The ordinary rank buckets establish the paired work invariant. -/
theorem refined_initial_invariant
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (hops : PolynomialOperations.IsCorrect K)
    (hgen : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar) (algorithmInputSet V ℓbar))
    (hr : RankedLayers K A f V)
    (hs : ∀ j v, v ∈ V j → 1 ≤ j ∧ j ≤ ℓbar) :
    EliminationWorkInvariant K A f ℓbar ℓbar (∅ : Set (Fin n → K)) #[]
      (terminalPairs (PolynomialOperations.applyMatrix f A) ℓbar (V ℓbar))
      (fun j => terminalPairs (PolynomialOperations.applyMatrix f A) j
        (Function.update V ℓbar [] j)) := by
  have he : initialPending (PolynomialOperations.applyMatrix f A) V ℓbar =
      fun j => terminalPairs (PolynomialOperations.applyMatrix f A) j (V j) := by
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
    Finset.notMem_empty, exists_false, Set.ofPred_false] using h

/-- Correctness for an arbitrary generating family with prescribed rank layers. -/
theorem computeRefinedJordanKrylovBasis_correct_of_generating
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n ℓbar m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (preprocess : Bool)
    (hops : PolynomialOperations.IsCorrect K)
    (hf : Irreducible f) (hm : f.Monic)
    (hmultiplicity : m = multiplicity f A.charpoly)
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
      (computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess : Set (Fin n → K)) := by
  rw [computeRefinedJordanKrylovBasis_eq_model]
  by_cases hz : ℓbar = 0
  · subst ℓbar
    simp only [refinedElimination, Id.run, Pure.pure,
      Finset.coe_empty, powerKernel_zero]
    exact ⟨empty_isKrylovGeneratingSet_bot K A, isJordanKrylovIndependent_empty K A⟩
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
        (refinedElimination K A f m ℓbar (W ℓbar) (Function.update W ℓbar []) ∅ 0 #[] :
          Set (Fin n → K)) :=
    refinedElimination_correct K hops A f hf hm m hmultiplicity ℓbar _ _ ∅ 0 #[]
      (by omega) le_rfl (by simp) (by simpa only [Finset.coe_empty] using refined_initial_invariant K A f W hops hg hr hs)
  cases preprocess with
  | false => exact finish U hug hur hus
  | true =>
    have hc := reduceKrylovGenerators_correct K hops A f U ℓbar _ hug hur hus
    exact finish _ hc.1 hc.2
      (reduceKrylovGenerators_support K hops A f U ℓbar (fun v hv => (hur ℓbar v hv).2.2) hus)

/-- Algorithms 1 and 3 produce a Jordan–Krylov basis from a spanning family
and its minimal annihilating polynomials, with or without preprocessing. -/
theorem computeRefinedJordanKrylovBasis_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin s → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin s → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (preprocess : Bool) (hops : PolynomialOperations.IsCorrect K) :
    IsJordanKrylovBasis K A (powerKernel K A f (multiplicity f (minpoly K A)))
      (computeRefinedJordanKrylovBasis K A f (computePrimaryGenerators K A e f p)
        (multiplicity f (minpoly K A)) (multiplicity f A.charpoly) preprocess :
          Set (Fin n → K)) := by
  apply computeRefinedJordanKrylovBasis_correct_of_generating K A f _ preprocess hops hf hm rfl
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
