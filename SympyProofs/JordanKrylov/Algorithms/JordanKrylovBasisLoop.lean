import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisInvariant
/-! # Verification of the imperative candidate loop

The proof model `candidateIteration` is used only to expose the loop state for
induction. `candidateLayer_eq_fold` connects it to the unchanged imperative body.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial
/-- A proof model of one iteration, matching the imperative body of Algorithm 2. -/
def candidateIteration (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (k : ℕ)
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) := Id.run do
  let F := PolynomialOperations.applyMatrix f A
  let d := f.toFinsupp.coeff.support.sup id
  let ℓ := k + 1
  let mut basis := basis
  let mut pending := pending
  let mut D := D
  let r := reducePairedColumn D v
  if r.top ≠ 0 then
    basis := Function.update basis ℓ (insert r.bottom (basis ℓ))
    let mut w := r
    for _ in List.range d do
      D := insertPairedColumn D w
      w := ⟨A *ᵥ w.top, A *ᵥ w.bottom⟩
  else if r.bottom ≠ 0 ∧ 1 < ℓ then
    let mut rank : ℕ := 0
    let mut terminal := r.bottom
    let mut w := r.bottom
    for j in List.range k do
      if rank = 0 then
        let next := F w
        if next = 0 then
          rank := j + 1
          terminal := w
        else
          w := next
    if 0 < rank then
      pending := Function.update pending rank
        (pending rank ++ [⟨terminal, r.bottom⟩])
  return (basis, pending, D)

theorem candidateIteration_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n ℓbar k : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (todo : List (PairedColumn K n)) (hle : k + 1 ≤ ℓbar)
    (h : EliminationWorkInvariant K A f ℓbar (k + 1) (acceptedGenerators basis) D
      (v :: todo) pending) :
    let out := candidateIteration K A f k basis pending D v
    EliminationWorkInvariant K A f ℓbar (k + 1) (acceptedGenerators out.1) out.2.2
      todo out.2.1 := by
  by_cases ht : (reducePairedColumn D v).top ≠ 0
  · simp only [candidateIteration, coefficientSupport_sup_eq_natDegree,
      List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
    rw [ite_eq_left ht]
    have hh := h.accept K A f hf hm _ D v todo pending (by omega) hle ht
    dsimp only at hh
    rw [← acceptedGenerators_insert basis (k + 1)] at hh
    exact hh
  · have hz : (reducePairedColumn D v).top = 0 := not_ne_iff.mp ht
    by_cases hb : (reducePairedColumn D v).bottom ≠ 0 ∧ 1 < k + 1
    · have hv := h.current v (List.mem_cons_self ..)
      have hk : (reducePairedColumn D v).bottom ∈ powerKernel K A f k := by
        simpa only [Nat.add_sub_cancel] using
          reducePairedColumn_mem_previous_powerKernel K A f D v h.table.paired hv.2 hz
      have hs := residualRankSearch_correct K hops A f (reducePairedColumn D v).bottom hb.1 hk
      simp only [Id.run] at hs
      simp only [candidateIteration, Id.run]
      rw [ite_eq_right ht, ite_eq_left hb]
      dsimp only [Bind.bind, Pure.pure] at hs ⊢
      simp only [Prod.mk.eta] at hs
      rw [hs]
      have hr : 0 < vectorRank K A f (reducePairedColumn D v).bottom :=
        (vectorRank_bounds K A f _ hb.1 hk).1
      simp only [hr, ite_true]
      exact h.requeue K A f _ D v todo pending hz hb.1
    · have hbzero : (reducePairedColumn D v).bottom = 0 := by
        by_cases hh : (reducePairedColumn D v).bottom = 0
        · exact hh
        · have hkle : ¬ 1 < k + 1 := fun hc => hb ⟨hh, hc⟩
          have hk : k = 0 := by omega
          subst k
          have hv := h.current v (List.mem_cons_self ..)
          apply reducePairedColumn_bottom_eq_zero_at_rank_one K D v _ _ hz
          · simpa using h.table.paired
          · simpa using hv.2
      simp only [candidateIteration, Id.run]
      rw [ite_eq_right ht, ite_eq_right hb]
      exact h.discard K A f _ D v todo pending hbzero
theorem candidateLayer_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n ℓbar k : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (todo : List (PairedColumn K n))
    (hle : k + 1 ≤ ℓbar)
    (h : EliminationWorkInvariant K A f ℓbar (k + 1) (acceptedGenerators basis) D todo pending) :
    let out := todo.foldl
      (fun s v => candidateIteration K A f k s.1 s.2.1 s.2.2 v) (basis, pending, D)
    EliminationWorkInvariant K A f ℓbar (k + 1) (acceptedGenerators out.1) out.2.2
      [] out.2.1 := by
  induction todo generalizing basis pending D with
  | nil => exact h
  | cons v todo ih =>
    exact ih _ _ _ (candidateIteration_correct K hops A f hf hm basis pending D v todo hle h)

theorem candidateIteration_basis
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (k : ℕ)
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) :
    (candidateIteration K A f k basis pending D v).1 =
      if (reducePairedColumn D v).top ≠ 0 then
        Function.update basis (k + 1) (insert (reducePairedColumn D v).bottom (basis (k + 1)))
      else basis := by
  unfold candidateIteration
  dsimp only [Id.run, Bind.bind, Pure.pure]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- Only positive layers up to the prescribed bound can contain accepted vectors. -/
def BasisLayerSupport {K : Type} {n : ℕ} (ℓbar : ℕ) (basis : ℕ → Finset (Fin n → K)) : Prop :=
  ∀ j v, v ∈ basis j → 1 ≤ j ∧ j ≤ ℓbar

theorem candidateIteration_support
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n ℓbar k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hs : BasisLayerSupport ℓbar basis) (hle : k + 1 ≤ ℓbar) :
    BasisLayerSupport ℓbar (candidateIteration K A f k basis pending D v).1 := by
  rw [candidateIteration_basis]
  split
  · intro j w hw
    by_cases he : j = k + 1
    · subst j; exact ⟨by omega, hle⟩
    · rw [Function.update_of_ne he] at hw
      exact hs j w hw
  · exact hs

theorem candidateLayer_eq_fold
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (k : ℕ)
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (todo : List (PairedColumn K n)) :
    (Id.run do
      let F := PolynomialOperations.applyMatrix f A
      let d := f.toFinsupp.coeff.support.sup id
      let ℓ := k + 1
      let mut basis := basis
      let mut pending := pending
      let mut D := D
      for v in todo do
        let r := reducePairedColumn D v
        if r.top ≠ 0 then
          basis := Function.update basis ℓ (insert r.bottom (basis ℓ))
          let mut w := r
          for _ in List.range d do
            D := insertPairedColumn D w
            w := ⟨A *ᵥ w.top, A *ᵥ w.bottom⟩
        else if r.bottom ≠ 0 ∧ 1 < ℓ then
          let mut rank : ℕ := 0
          let mut terminal := r.bottom
          let mut w := r.bottom
          for j in List.range k do
            if rank = 0 then
              let next := F w
              if next = 0 then
                rank := j + 1
                terminal := w
              else
                w := next
          if 0 < rank then
            pending := Function.update pending rank
              (pending rank ++ [⟨terminal, r.bottom⟩])
      return (basis, pending, D)) =
      todo.foldl (fun s v => candidateIteration K A f k s.1 s.2.1 s.2.2 v)
        (basis, pending, D) := by
  have hy {α β : Type} (xs : List α) (s : β) (step : β → α → β) :
      (forIn xs s (fun a b => ForInStep.yield (step b a)) : Id β) = xs.foldl step s :=
    List.forIn_pure_yield_eq_foldl (m := Id) (fun a b => step b a) s
  simp only [candidateIteration, Id.run, Bind.bind, Pure.pure, ← apply_ite]
  simp only [hy, Prod.mk.eta]

theorem candidateLayer_support
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K] {n ℓbar k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (basis : ℕ → Finset (Fin n → K)) (pending : ℕ → List (PairedColumn K n))
    (D : Array (Fin n × PairedColumn K n)) (todo : List (PairedColumn K n))
    (hs : BasisLayerSupport ℓbar basis) (hle : k + 1 ≤ ℓbar) :
    BasisLayerSupport ℓbar
      (todo.foldl (fun s v => candidateIteration K A f k s.1 s.2.1 s.2.2 v)
        (basis, pending, D)).1 := by
  induction todo generalizing basis pending D with
  | nil => exact hs
  | cons v todo ih =>
    exact ih _ _ _ (candidateIteration_support K A f basis pending D v hs hle)

private theorem mem_basis_union_fold {K : Type} [DecidableEq K] {n : ℕ}
    (basis : ℕ → Finset (Fin n → K)) (ks : List ℕ) (acc : Finset (Fin n → K)) (v : Fin n → K) :
    v ∈ ks.foldl (fun s k => s ∪ basis (k + 1)) acc ↔
      v ∈ acc ∨ ∃ k ∈ ks, v ∈ basis (k + 1) := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih => simp [List.foldl_cons, ih, or_assoc]

/-- The final union loop returns exactly the accepted set tracked by the invariant. -/
theorem collectBasis_eq_acceptedGenerators
    {K : Type} [DecidableEq K] {n ℓbar : ℕ} (basis : ℕ → Finset (Fin n → K))
    (hs : BasisLayerSupport ℓbar basis) :
    ((Id.run do
      let mut result : Finset (Fin n → K) := ∅
      for k in List.range ℓbar do
        result := result ∪ basis (k + 1)
      return result) : Set (Fin n → K)) = acceptedGenerators basis := by
  ext v
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  change v ∈ (List.range ℓbar).foldl (fun s k => s ∪ basis (k + 1)) ∅ ↔ _
  simp only [mem_basis_union_fold, Finset.notMem_empty, false_or, List.mem_range,
    acceptedGenerators, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hv⟩; exact ⟨k + 1, hv⟩
  · rintro ⟨j, hj⟩
    have hb := hs j v hj
    refine ⟨j - 1, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel hb.1] using hj

end SympyProofs.JordanKrylov
