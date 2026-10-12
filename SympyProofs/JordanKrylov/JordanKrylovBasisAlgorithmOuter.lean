import SympyProofs.JordanKrylov.JordanKrylovBasisAlgorithmLoop
/-! # Descending-layer verification for Algorithm 2

The proof model exposes the outer loop for induction. Initialization supplies
its invariant; rank one supplies the final basis property.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial
/-- Proof model for a rank layer after the top-layer special case. -/
def ordinaryLayerIteration (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (k : ℕ)
    (s : (ℕ → Finset (Vec K n)) × (ℕ → List (PairedColumn K n)) ×
      Array (Fin n × PairedColumn K n)) :=
  let out := (s.2.1 (k + 1)).foldl
    (fun t v => candidateIteration K A f k t.1 t.2.1 t.2.2 v)
    (s.1, Function.update s.2.1 (k + 1) [], s.2.2)
  (out.1, out.2.1, if 1 < k + 1 then out.2.2.map
    (fun (i, w) => (i, (⟨w.top, PolynomialOperations.applyMatrix f A w.bottom⟩ : PairedColumn K n)))
    else out.2.2)

 theorem remainingLayers_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n ℓbar : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (k : ℕ) (basis : ℕ → Finset (Vec K n)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (hle : k + 1 ≤ ℓbar)
    (h : EliminationWorkInvariant K A f ℓbar (k + 1) (acceptedGenerators basis) D
      (pending (k + 1)) (Function.update pending (k + 1) [])) :
    let out := (List.range (k + 1)).reverse.foldl
      (fun s j => ordinaryLayerIteration K A f j s) (basis, pending, D)
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) (acceptedGenerators out.1) := by
  induction k generalizing basis pending D with
  | zero =>
    have hh := candidateLayer_correct K hops A f hf hm basis
      (Function.update pending 1 []) D (pending 1) hle h
    simpa only [List.range_succ, List.range_zero, List.nil_append, List.reverse_singleton,
      List.foldl_cons, List.foldl_nil, ordinaryLayerIteration, lt_self_iff_false, ite_false] using
      hh.finish K A f _ _ _
  | succ k ih =>
    have hh := candidateLayer_correct K hops A f hf hm basis
      (Function.update pending (k + 1 + 1) []) D (pending (k + 1 + 1)) hle h
    have hn := hh.next_layer K hops A f (by omega) _ _ _
    have hr := ih _ _ _ (by omega) hn
    simpa only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.foldl_cons, List.foldl_append, List.foldl_nil, ordinaryLayerIteration,
      show 1 < k + 1 + 1 by omega, ite_true] using hr
theorem ordinaryLayerIteration_support
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n ℓbar k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (s : (ℕ → Finset (Vec K n)) × (ℕ → List (PairedColumn K n)) ×
      Array (Fin n × PairedColumn K n))
    (hs : BasisLayerSupport ℓbar s.1) (hle : k + 1 ≤ ℓbar) :
    BasisLayerSupport ℓbar (ordinaryLayerIteration K A f k s).1 :=
  candidateLayer_support K A f s.1 _ s.2.2 _ hs hle

theorem remainingLayers_support
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ks : List ℕ)
    (s : (ℕ → Finset (Vec K n)) × (ℕ → List (PairedColumn K n)) ×
      Array (Fin n × PairedColumn K n))
    (hs : BasisLayerSupport ℓbar s.1) (hle : ∀ k ∈ ks, k + 1 ≤ ℓbar) :
    BasisLayerSupport ℓbar
      (ks.foldl (fun s j => ordinaryLayerIteration K A f j s) s).1 := by
  induction ks generalizing s with
  | nil => exact hs
  | cons k ks ih =>
    exact ih _ (ordinaryLayerIteration_support K A f s hs (hle k (List.mem_cons_self ..)))
      (fun j hj => hle j (List.mem_cons_of_mem _ hj))

/-- Closed form of the already-verified initialization loop. -/
def initialPending {K : Type} {n : ℕ} (F : Vec K n → Vec K n)
    (V : ℕ → List (Vec K n)) (ℓbar ℓ : ℕ) : List (PairedColumn K n) :=
  if 1 ≤ ℓ ∧ ℓ ≤ ℓbar then (V ℓ).map (fun v => ⟨F^[ℓ - 1] v, v⟩) else []

theorem pairedListSpace_map_pair (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (top : Vec K n → Vec K n) (vs : List (Vec K n)) :
    pairedListSpace K A (vs.map (fun v => ⟨top v, v⟩)) =
      ⨆ v ∈ vs, krylovSpace K A v := by
  induction vs with
  | nil => simp [pairedListSpace]
  | cons v vs ih =>
    simp only [List.map_cons, pairedListSpace_cons, ih, List.mem_cons, iSup_or, iSup_sup_eq]
    simp

theorem pendingSpace_initialPending (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (F : Vec K n → Vec K n)
    (V : ℕ → List (Vec K n)) (ℓbar : ℕ) :
    pendingSpace K A (initialPending F V ℓbar) =
      generatorSpace K A (algorithmInputSet V ℓbar) := by
  apply le_antisymm
  · apply iSup_le
    intro j
    change pairedListSpace K A (initialPending F V ℓbar j) ≤ generatorSpace K A (algorithmInputSet V ℓbar)
    by_cases hj : 1 ≤ j ∧ j ≤ ℓbar
    · simp only [initialPending, hj, and_self, ite_true, pairedListSpace_map_pair]
      apply iSup_le
      intro v
      apply iSup_le
      intro hv
      exact le_iSup_of_le v (le_iSup_of_le ⟨j, hj.1, hj.2, hv⟩ le_rfl)
    · simp [initialPending, hj]
  · apply iSup_le
    intro v
    apply iSup_le
    rintro ⟨j, hpos, hle, hv⟩
    apply le_iSup_of_le j
    simp only [initialPending, hpos, hle, and_self, ite_true, pairedListSpace_map_pair]
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

theorem initialPending_valid
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Vec K n))
    (hops : PolynomialOperations.IsCorrect (K := K))
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ)
    (j : ℕ) (v : PairedColumn K n)
    (hv : v ∈ initialPending (PolynomialOperations.applyMatrix f A) V ℓbar j) :
    1 ≤ j ∧ j ≤ ℓbar ∧ ValidLayerColumn K A f j v ∧
      v.bottom ≠ 0 ∧ vectorRank K A f v.bottom = j := by
  unfold initialPending at hv
  split at hv
  · rename_i hj
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hker := algorithmInput_mem_powerKernel K A f V hgenerating hj.1 hj.2 hw
    have hr := hranks j hj.1 hj.2 w hw
    refine ⟨hj.1, hj.2, ⟨?_, ?_⟩, algorithmInput_ne_zero K A f V hranks hj.1 hj.2 hw, hr⟩
    · simpa only [hr] using mem_powerKernel_vectorRank K A f w hker
    · exact applyMatrix_iterate_eq_pow_mulVec K hops A f w (j - 1)
  · simp at hv

theorem EliminationTableInvariant.empty
    (K : Subfield ℂ) {n ℓbar ℓ : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    EliminationTableInvariant K A f ℓbar ℓ ∅ #[] := by
  constructor
  · exact isJordanKrylovIndependent_empty K A
  · simp
  · simp [PairedEchelon]
  · simp
  · simp
  · simp
  · simp [pairedTopSpan]

/-- The paper's input contract establishes the full work invariant at the top layer. -/
theorem initial_workInvariant
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Vec K n))
    (hops : PolynomialOperations.IsCorrect (K := K))
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ) :
    let pending := initialPending (PolynomialOperations.applyMatrix f A) V ℓbar
    EliminationWorkInvariant K A f ℓbar ℓbar (acceptedGenerators (fun _ => ∅)) #[]
      (pending ℓbar) (Function.update pending ℓbar []) := by
  dsimp only
  have he : acceptedGenerators (fun _ => (∅ : Finset (Vec K n))) = ∅ := by
    ext v; simp [acceptedGenerators]
  rw [he]
  refine ⟨EliminationTableInvariant.empty K A f, ?_, ?_, ?_⟩
  · intro v hv
    exact (initialPending_valid K A f V hops hgenerating hranks ℓbar v hv).2.2.1
  · intro j v hv
    by_cases heq : j = ℓbar
    · subst j; simp at hv
    · rw [Function.update_of_ne heq] at hv
      have hh := initialPending_valid K A f V hops hgenerating hranks j v hv
      exact ⟨hh.1, by omega, hh.2.2.1⟩
  · have hh : powerKernel K A f ℓbar =
        pendingSpace K A (initialPending (PolynomialOperations.applyMatrix f A) V ℓbar) := by
      rw [pendingSpace_initialPending]
      exact hgenerating
    rw [hh, pendingSpace_extract K A _ ℓbar]
    simp [workSpace]

end SympyProofs.JordanKrylov
