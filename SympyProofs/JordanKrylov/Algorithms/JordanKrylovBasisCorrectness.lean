import SympyProofs.JordanKrylov.Algorithms.PrimaryGeneratingCorrectness
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisOuter
/-! # Full correctness of Algorithm 2

`computeJordanKrylovBasis_correct` proves the postcondition of the actual
imperative algorithm under the explicit input hypotheses. The proof
connects its early-return control flow to the verified descending-layer model.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial
abbrev EliminationState (K : Type) (n : ℕ) :=
  (ℕ → List (Fin n → K)) × (ℕ → List (PairedColumn K n)) × Array (Fin n × PairedColumn K n)

def algorithmOuterIteration (K : Type) [Field K] [DecidableEq K] [Operations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓbar m k : ℕ)
    (s : Option (ℕ → List (Fin n → K)) × EliminationState K n) :
    ForInStep (Option (ℕ → List (Fin n → K)) × EliminationState K n) :=
  let ℓ := k + 1
  let basis := s.2.1
  let pending := s.2.2.1
  let D := s.2.2.2
  let layer := pending ℓ
  let pending := Function.update pending ℓ []
  let finish := fun basis D layer =>
    let out := layer.foldl (fun t v => candidateIteration K A f k t.1 t.2.1 t.2.2 v)
      (basis, pending, D)
    ForInStep.yield (none, out.1, out.2.1,
      if 1 < ℓ then out.2.2.map (fun (i, w) =>
        (i, (⟨w.top, Operations.applyMatrix f A w.bottom⟩ : PairedColumn K n)))
      else out.2.2)
  if ℓ = ℓbar then
    if let v :: rest := layer then
      let basis := Function.update basis ℓ [v.bottom]
      if ℓ = m then .done (some basis, basis, pending, D)
      else
        let out := (List.range (f.natDegree)).foldl
          (fun (t : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
            (insertPairedColumn t.1 t.2, ⟨A *ᵥ t.2.top, A *ᵥ t.2.bottom⟩)) (D, v)
        finish basis out.1 rest
    else finish basis D layer
  else finish basis D layer

/-- An Id loop whose body always yields is a left fold. -/
theorem forIn_yield_eq_foldl {α β : Type} (xs : List α) (s : β) (step : β → α → β) :
    (forIn xs s (fun a b => ForInStep.yield (step b a)) : Id β) = xs.foldl step s :=
  List.forIn_pure_yield_eq_foldl (m := Id) (fun a b => step b a) s

theorem initializePending_fold_eq {K : Type} {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (V : ℕ → List (Fin n → K)) (ℓbar : ℕ) :
    (List.range ℓbar).reverse.foldl
      (fun (pending : ℕ → List (PairedColumn K n)) k => Function.update pending (k + 1)
        ((V (k + 1)).foldl (fun layer v => layer ++
          [PairedColumn.mk ((List.range k).foldl (fun w _ => F w) v) v]) []))
      (fun _ => []) = initialPending F V ℓbar := by
  funext ℓ
  have h := initializePending_loop_eq F V ℓbar ℓ
  simp only [Id.run, Bind.bind, Pure.pure, forIn_yield_eq_foldl] at h
  exact h

theorem computeJordanKrylovBasis_eq_outerModel
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) :
    computeJordanKrylovBasis K A f V ℓbar m =
      let out := (forIn (List.range ℓbar).reverse
        (none, (fun _ => []), initialPending (Operations.applyMatrix f A) V ℓbar, #[])
        (fun k s => algorithmOuterIteration K A f ℓbar m k s) : Id _)
      out.1.getD out.2.1 := by
  dsimp only
  simp only [computeJordanKrylovBasis, algorithmOuterIteration, candidateIteration,
    Id.run, Bind.bind, Pure.pure, ← apply_ite]
  simp only [List.forIn_map, forIn_yield_eq_foldl, List.foldl_map, Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Prod.mk.eta, initializePending_fold_eq]
  have hmatch (result : Option (ℕ → List (Fin n → K))) (fallback : ℕ → List (Fin n → K)) :
      Break.runK (β := Id (ℕ → List (Fin n → K))) result (fun _ => fallback) (fun r => r) =
        result.getD fallback := by
    cases result <;> rfl
  unfold Break.runK at hmatch
  rw [hmatch]
  congr 1

theorem algorithmOuterIteration_ordinary
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓbar m k : ℕ)
    (s : Option (ℕ → List (Fin n → K)) × EliminationState K n) (hne : k + 1 ≠ ℓbar) :
    algorithmOuterIteration K A f ℓbar m k s =
      ForInStep.yield (none, ordinaryLayerIteration K A f k s.2) := by
  simp only [algorithmOuterIteration, hne, ite_false, ordinaryLayerIteration]

theorem outerLoop_below_top
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓbar m : ℕ)
    (ks : List ℕ) (s : EliminationState K n) (hle : ∀ k ∈ ks, k + 1 ≠ ℓbar) :
    (forIn ks (none, s) (fun k s => algorithmOuterIteration K A f ℓbar m k s) : Id _) =
      (none, ks.foldl (fun s k => ordinaryLayerIteration K A f k s) s) := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rw [List.forIn_cons, algorithmOuterIteration_ordinary K A f ℓbar m k _
      (hle k (List.mem_cons_self ..))]
    exact ih _ (fun j hj => hle j (List.mem_cons_of_mem _ hj))

@[simp] theorem reducePairedColumn_empty {K : Type} [Field K] {n : ℕ} (v : PairedColumn K n) :
    reducePairedColumn #[] v = v := by
  simp [reducePairedColumn, Array.forIn_pure_yield_eq_foldl]

theorem algorithmOuterIteration_initial_noEarly
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m k : ℕ)
    (pending : ℕ → List (PairedColumn K n)) (hne : k + 1 ≠ m)
    (hcolumns : ∀ v ∈ pending (k + 1), v.top ≠ 0) :
    algorithmOuterIteration K A f (k + 1) m k (none, (fun _ => []), pending, #[]) =
      ForInStep.yield (none, ordinaryLayerIteration K A f k ((fun _ => []), pending, #[])) := by
  cases he : pending (k + 1) with
  | nil => simp [algorithmOuterIteration, ordinaryLayerIteration, he]
  | cons v rest =>
    have hv : v.top ≠ 0 := hcolumns v (by simp [he])
    simp only [algorithmOuterIteration, ordinaryLayerIteration, he, ite_true, hne,
      ite_false, List.foldl_cons, candidateIteration, reducePairedColumn_empty,
      Id.run, Bind.bind, Pure.pure, ← apply_ite, forIn_yield_eq_foldl,
      Prod.mk.eta]
    rw [ite_eq_left hv]

theorem outerLoop_eq_ordinary_of_initial_yield
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m k : ℕ) (s : EliminationState K n)
    (hfirst : algorithmOuterIteration K A f (k + 1) m k (none, s) =
      ForInStep.yield (none, ordinaryLayerIteration K A f k s)) :
    (forIn (List.range (k + 1)).reverse (none, s)
      (fun j t => algorithmOuterIteration K A f (k + 1) m j t) : Id _) =
      (none, (List.range (k + 1)).reverse.foldl
        (fun t j => ordinaryLayerIteration K A f j t) s) := by
  rw [List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.forIn_cons, hfirst, List.foldl_cons]
  apply outerLoop_below_top
  intro j hj
  simp only [List.mem_reverse, List.mem_range] at hj
  omega

theorem computeJordanKrylovBasis_correct_of_initial_yield
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n k m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (hops : Operations.IsCorrect K)
    (hf : Irreducible f) (hm : f.Monic)
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f (k + 1))
      (algorithmInputSet V (k + 1)))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ (k + 1) → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ)
    (hfirst : algorithmOuterIteration K A f (k + 1) m k
        (none, (fun _ => []), initialPending (Operations.applyMatrix f A) V (k + 1), #[]) =
      ForInStep.yield (none, ordinaryLayerIteration K A f k
        ((fun _ => []), initialPending (Operations.applyMatrix f A) V (k + 1), #[]))) :
    IsJordanKrylovBasis K A (powerKernel K A f (k + 1))
      (acceptedGenerators (computeJordanKrylovBasis K A f V (k + 1) m)) ∧
      BasisLayerRanks K A f (computeJordanKrylovBasis K A f V (k+1) m) := by
  rw [computeJordanKrylovBasis_eq_outerModel,
    outerLoop_eq_ordinary_of_initial_yield K A f m k _ hfirst]
  simp only [Option.getD_none]
  let s : EliminationState K n := ((fun _ => []),
    initialPending (Operations.applyMatrix f A) V (k + 1), #[])
  let out := (List.range (k + 1)).reverse.foldl (fun t j => ordinaryLayerIteration K A f j t) s
  exact ⟨remainingLayers_correct K hops A f hf hm k
    s.1 s.2.1 s.2.2 le_rfl (initial_workInvariant K A f V hops hgenerating hranks),
    remainingLayers_ranks K hops A f hf hm k s.1 s.2.1 s.2.2 le_rfl
      (initial_workInvariant K A f V hops hgenerating hranks) (basisLayerRanks_empty K A f)⟩

/-- Algorithm 2 returns a Jordan–Krylov basis of the primary power kernel from
a generating family with the prescribed ranks and characteristic multiplicity.
Each returned layer retains its exact positive rank. -/
theorem computeJordanKrylovBasis_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n ℓbar m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Fin n → K))
    (hops : Operations.IsCorrect K)
    (hf : Irreducible f) (hm : f.Monic)
    (hmultiplicity : m = multiplicity f A.charpoly)
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar)
      (acceptedGenerators (computeJordanKrylovBasis K A f V ℓbar m)) ∧
      BasisLayerRanks K A f (computeJordanKrylovBasis K A f V ℓbar m) := by
  cases ℓbar with
  | zero =>
    rw [computeJordanKrylovBasis_eq_outerModel]
    simp [List.forIn_nil, Pure.pure, powerKernel_zero, acceptedGenerators, basisLayerRanks_empty]
  | succ k =>
    let pending := initialPending (Operations.applyMatrix f A) V (k + 1)
    have hcolumns (v : PairedColumn K n) (hv : v ∈ pending (k + 1)) : v.top ≠ 0 := by
      have hh := initialPending_valid K A f V hops hgenerating hranks (k + 1) v hv
      have hnot := ((vectorRank_eq_iff K A f v.bottom hh.2.2.1.1 hh.1).mp hh.2.2.2.2).2
      intro hz
      exact hnot (hh.2.2.1.2.symm.trans hz)
    cases he : pending (k + 1) with
    | nil =>
      apply computeJordanKrylovBasis_correct_of_initial_yield K A f V hops hf hm hgenerating hranks
      change algorithmOuterIteration K A f (k + 1) m k (none, (fun _ => []), pending, #[]) =
        ForInStep.yield (none, ordinaryLayerIteration K A f k ((fun _ => []), pending, #[]))
      simp [algorithmOuterIteration, ordinaryLayerIteration, he]
    | cons v rest =>
      by_cases hearly : k + 1 = m
      · have hv : v ∈ pending (k + 1) := by simp [he]
        have hh := initialPending_valid K A f V hops hgenerating hranks (k + 1) v hv
        have hb : IsJordanKrylovBasis K A (powerKernel K A f (k + 1)) {v.bottom} :=
          singleton_isJordanKrylovBasis_of_rank_eq_charpoly_multiplicity K A f
            hf hm v.bottom hh.2.2.2.1 hh.2.2.1.1
            (hh.2.2.2.2.trans (hearly.trans hmultiplicity))
        have hfirst : algorithmOuterIteration K A f (k + 1) m k
            (none, (fun _ => []), pending, #[]) =
            ForInStep.done (some (Function.update (fun _ => []) (k + 1) [v.bottom]), Function.update (fun _ => []) (k + 1) [v.bottom],
              Function.update pending (k + 1) [], #[]) := by
          simp only [algorithmOuterIteration, ite_true, he, ite_eq_left hearly]
        rw [computeJordanKrylovBasis_eq_outerModel]
        rw [List.range_succ, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.forIn_cons, hfirst]
        have hr := (basisLayerRanks_empty K A f).cons K A f (fun _ => []) (k+1) v.bottom
          (by omega) hh.2.2.2.2
        simpa only [Bind.bind, Pure.pure, Option.getD_some, acceptedGenerators_singleton] using And.intro hb hr
      · apply computeJordanKrylovBasis_correct_of_initial_yield K A f V hops hf hm hgenerating hranks
        exact algorithmOuterIteration_initial_noEarly K A f m k pending hearly hcolumns

/-- Algorithm 1 supplies Algorithm 2's rank-indexed input directly. -/
theorem computeJordanKrylovBasis_fromPrimaryGenerators_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin s → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin s → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (hops : Operations.IsCorrect K) :
    IsJordanKrylovBasis K A (powerKernel K A f (multiplicity f (minpoly K A)))
      (acceptedGenerators (computeJordanKrylovBasis K A f (primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)))
        (multiplicity f (minpoly K A)) (multiplicity f A.charpoly))) ∧
      BasisLayerRanks K A f (computeJordanKrylovBasis K A f (primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)))
        (multiplicity f (minpoly K A)) (multiplicity f A.charpoly)) := by
  apply computeJordanKrylovBasis_correct K A f _ hops hf hm rfl
  · rw [primaryGeneratorsModel_inputSet_eq K hops A e f hf hm p
      (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)
      (fun i => by
        rw [multiplicity_minpoly_eq_max_spanning K A e he f hf hm, hp i]
        exact Finset.le_sup (f := fun j => multiplicity f
          (minimalAnnihilatingPolynomial K A (e j))) (Finset.mem_univ i))]
    exact primaryGeneratorsModel_correct K hops A e he f hf hm p hp
  · intro ℓ _ _ v hv
    exact primaryGeneratorsModel_ranks K hops A e f hf hm p hp ℓ v hv

end SympyProofs.JordanKrylov
