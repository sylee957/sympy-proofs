import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisAlgorithm
import SympyProofs.JordanKrylov.Mathematics.IndependentExtension
import SympyProofs.JordanKrylov.Mathematics.PrimaryKernelDimension

/-! # Verification of Jordan–Krylov elimination

The input contract contains mathematical input assumptions only. These lemmas
verify initialization, column insertion, reduction, bounded rank descent, and
the characteristic-multiplicity early return. The full executable correctness
theorem is in `JordanKrylovBasisAlgorithmCorrectness`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- The generators in the positive layers inspected by Algorithm 2. -/
def algorithmInputSet {K : Type*} {n : ℕ} (V : ℕ → List (Vec K n))
    (ℓbar : ℕ) : Set (Vec K n) := {v | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ ℓbar ∧ v ∈ V ℓ}

/-- The generation precondition puts every processed vector in the primary kernel. -/
theorem algorithmInput_mem_powerKernel
    (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Vec K n))
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    {ℓ : ℕ} (hpos : 1 ≤ ℓ) (hle : ℓ ≤ ℓbar) {v : Vec K n} (hv : v ∈ V ℓ) :
    v ∈ powerKernel K A f ℓbar :=
  hgenerating.subset K A _ _ ⟨ℓ, hpos, hle, hv⟩

/-- Under the paper's rank convention all processed input vectors are nonzero. -/
theorem algorithmInput_ne_zero
    (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Vec K n))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ)
    {ℓ : ℕ} (hpos : 1 ≤ ℓ) (hle : ℓ ≤ ℓbar) {v : Vec K n} (hv : v ∈ V ℓ) :
    v ≠ 0 := by
  intro hz
  have hr := hranks ℓ hpos hle v hv
  rw [hz, vectorRank_zero] at hr
  omega

/-- Remark 4 for the executable reduction: zero in the upper half forces the
lower residual into the preceding power kernel. -/
theorem reducePairedColumn_mem_previous_powerKernel
    (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = (aeval A f) ^ (ℓ - 1) *ᵥ iw.2.bottom)
    (hv : v.top = (aeval A f) ^ (ℓ - 1) *ᵥ v.bottom)
    (hz : (reducePairedColumn D v).top = 0) :
    (reducePairedColumn D v).bottom ∈ powerKernel K A f (ℓ - 1) := by
  have hr := reducePairedColumn_top_eq ((aeval A f) ^ (ℓ - 1)).mulVecLin D v hD hv
  exact hr.symm.trans hz

/-- A nonzero residual belongs to a strictly lower positive rank layer. -/
theorem reducePairedColumn_rank_lt
    (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = (aeval A f) ^ (ℓ - 1) *ᵥ iw.2.bottom)
    (hv : v.top = (aeval A f) ^ (ℓ - 1) *ᵥ v.bottom)
    (hz : (reducePairedColumn D v).top = 0)
    (hne : (reducePairedColumn D v).bottom ≠ 0) :
    1 ≤ vectorRank K A f (reducePairedColumn D v).bottom ∧
      vectorRank K A f (reducePairedColumn D v).bottom < ℓ := by
  have hb := vectorRank_bounds K A f _ hne
    (reducePairedColumn_mem_previous_powerKernel K A f D v hD hv hz)
  omega

/-- A zero residual at rank one can be discarded: the lower half also vanishes. -/
theorem reducePairedColumn_bottom_eq_zero_at_rank_one
    (K : Subfield ℂ) {n : ℕ}
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = iw.2.bottom)
    (hv : v.top = v.bottom) (hz : (reducePairedColumn D v).top = 0) :
    (reducePairedColumn D v).bottom = 0 := by
  have hr := reducePairedColumn_top_eq (LinearMap.id : Module.End K (Vec K n)) D v hD hv
  exact hr.symm.trans hz

/-- Case 1: a nonzero upper remainder has exactly the current rank. -/
theorem reducePairedColumn_rank_eq
    (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hℓ : 1 ≤ ℓ)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.top = (aeval A f) ^ (ℓ - 1) *ᵥ iw.2.bottom)
    (hv : v.top = (aeval A f) ^ (ℓ - 1) *ᵥ v.bottom)
    (hDker : ∀ iw ∈ D.toList, iw.2.bottom ∈ powerKernel K A f ℓ)
    (hvker : v.bottom ∈ powerKernel K A f ℓ)
    (hne : (reducePairedColumn D v).top ≠ 0) :
    vectorRank K A f (reducePairedColumn D v).bottom = ℓ := by
  have hk := reducePairedColumn_bottom_mem (powerKernel K A f ℓ) D v hDker hvker
  apply (vectorRank_eq_iff K A f _ hk hℓ).mpr
  refine ⟨hk, ?_⟩
  have hr := reducePairedColumn_top_eq ((aeval A f) ^ (ℓ - 1)).mulVecLin D v hD hv
  intro hz
  exact hne (hr.trans hz)

/-- Case 1: accepting the executable remainder preserves Jordan–Krylov
independence when the stored upper span represents the accepted terminal spaces. -/
theorem reducePairedColumn_insert_independent
    (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (hℓ : 1 ≤ ℓ) (hle : ℓ ≤ ℓbar)
    (B : Set (Vec K n)) (hB : IsJordanKrylovIndependent K A B)
    (hBker : B ⊆ (powerKernel K A f ℓbar : Set (Vec K n)))
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hech : PairedEchelon D.toList)
    (hspan : Submodule.span K {w | ∃ iw ∈ D.toList, w = iw.2.top} =
      ⨆ b : B, krylovSpace K A (terminalVector K A f b.val))
    (hD : ∀ iw ∈ D.toList, iw.2.top = (aeval A f) ^ (ℓ - 1) *ᵥ iw.2.bottom)
    (hv : v.top = (aeval A f) ^ (ℓ - 1) *ᵥ v.bottom)
    (hDker : ∀ iw ∈ D.toList, iw.2.bottom ∈ powerKernel K A f ℓ)
    (hvker : v.bottom ∈ powerKernel K A f ℓ)
    (hne : (reducePairedColumn D v).top ≠ 0) :
    IsJordanKrylovIndependent K A (insert (reducePairedColumn D v).bottom B) := by
  have hk := reducePairedColumn_bottom_mem (powerKernel K A f ℓ) D v hDker hvker
  apply hB.insert_of_terminalVector_not_mem K A f hf hm B hBker _
    (powerKernel_monotone K A f hle hk)
  have hrank := reducePairedColumn_rank_eq K A f hℓ D v hD hv hDker hvker hne
  have hr := reducePairedColumn_top_eq ((aeval A f) ^ (ℓ - 1)).mulVecLin D v hD hv
  have hn := reducePairedColumn_top_not_mem_span D hech v hne
  rw [hspan] at hn
  rw [hr] at hn
  simpa only [terminalVector, hrank, Matrix.mulVecLin_apply] using hn

/-- Replacing a candidate by its elimination residual preserves the generated
space after adjoining the already accepted invariant subspace. -/
theorem krylovSpace_sup_eq_of_sub_mem
    (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Vec K n)) (hW : ∀ x ∈ W, A *ᵥ x ∈ W)
    (v r : Vec K n) (hvr : v - r ∈ W) :
    W ⊔ krylovSpace K A v = W ⊔ krylovSpace K A r := by
  have hinv (u : Vec K n) (x : Vec K n) (hx : x ∈ W ⊔ krylovSpace K A u) :
      A *ᵥ x ∈ W ⊔ krylovSpace K A u := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hW a ha))
      (Submodule.mem_sup_right (mulVec_mem_krylovSpace K A u b hb))
  apply le_antisymm
  · apply sup_le le_sup_left
    apply krylovSpace_le K A v _ _ (hinv r)
    have ha : v - r ∈ W ⊔ krylovSpace K A r := Submodule.mem_sup_left hvr
    have hb : r ∈ W ⊔ krylovSpace K A r := Submodule.mem_sup_right (self_mem_krylovSpace K A r)
    simpa using Submodule.add_mem _ ha hb
  · apply sup_le le_sup_left
    apply krylovSpace_le K A r _ _ (hinv v)
    have ha : v - r ∈ W ⊔ krylovSpace K A v := Submodule.mem_sup_left hvr
    have hb : v ∈ W ⊔ krylovSpace K A v := Submodule.mem_sup_right (self_mem_krylovSpace K A v)
    simpa using Submodule.sub_mem _ hb ha

/-- The executable column reduction preserves the generated space, whether
its remainder is accepted, requeued, or discarded. -/
theorem reducePairedColumn_preserves_generating_space
    (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Vec K n)) (hW : ∀ x ∈ W, A *ᵥ x ∈ W)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hD : ∀ iw ∈ D.toList, iw.2.bottom ∈ W) :
    W ⊔ krylovSpace K A v.bottom =
      W ⊔ krylovSpace K A (reducePairedColumn D v).bottom :=
  krylovSpace_sup_eq_of_sub_mem K A W hW _ _
    (reducePairedColumn_bottom_sub_mem W D v hD)

/-- State of the bounded scan after any number of iterations. -/
theorem boundedRankSearch_fold_state {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : Vec K n → Vec K n) (v : Vec K n) (r : ℕ) (hr : 0 < r)
    (hkill : F^[r] v = 0) (hbefore : ∀ j < r, F^[j] v ≠ 0) (k : ℕ) :
    (List.range k).foldl
      (fun (s : ℕ × Vec K n × Vec K n) j =>
        if s.1 = 0 then
          if F s.2.2 = 0 then (j + 1, s.2.2, s.2.2)
          else (s.1, s.2.1, F s.2.2)
        else s) (0, v, v) =
      if k < r then (0, v, F^[k] v)
      else (r, F^[r - 1] v, F^[r - 1] v) := by
  induction k with
  | zero => simp [hr]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    by_cases hk : k < r
    · simp only [ite_eq_left hk, ite_true]
      by_cases hs : k + 1 < r
      · have hn : F (F^[k] v) ≠ 0 := by
          simpa only [Function.iterate_succ_apply'] using hbefore (k + 1) hs
        simp [hn, hs, Function.iterate_succ_apply']
      · have he : k + 1 = r := by omega
        have hz : F (F^[k] v) = 0 := by
          simpa only [← he, Function.iterate_succ_apply'] using hkill
        simp [hz, ← he]
    · have hs : ¬ k + 1 < r := by omega
      simp [hk, hs, Nat.ne_of_gt hr]
/-- Once the bound reaches the first vanishing iterate, the scan has found it. -/
theorem boundedRankSearch_correct {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : Vec K n → Vec K n) (v : Vec K n) (r k : ℕ) (hr : 0 < r) (hk : r ≤ k)
    (hkill : F^[r] v = 0) (hbefore : ∀ j < r, F^[j] v ≠ 0) :
    (Id.run do
      let mut rank : ℕ := 0
      let mut terminal := v
      let mut w := v
      for j in List.range k do
        if rank = 0 then
          let next := F w
          if next = 0 then
            rank := j + 1
            terminal := w
          else
            w := next
      return (rank, terminal, w)) = (r, F^[r - 1] v, F^[r - 1] v) := by
  simp only [Id.run, ← apply_ite, List.forIn_pure_yield_eq_foldl, pure_bind]
  exact (boundedRankSearch_fold_state F v r hr hkill hbefore k).trans
    (ite_eq_right (by omega))

theorem applyMatrix_iterate_eq_pow_mulVec
    (K : Subfield ℂ) [PolynomialOperations K] {n : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Vec K n) (j : ℕ) :
    (PolynomialOperations.applyMatrix f A)^[j] v = (aeval A f)^j *ᵥ v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', hops.applyMatrix_eq, ih,
      pow_succ', Matrix.mulVec_mulVec]

theorem applyMatrix_iterate_ne_zero_of_lt_vectorRank
    (K : Subfield ℂ) [PolynomialOperations K] {n j : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Vec K n)
    (hv : v ≠ 0)
    (hj : j < vectorRank K A f v) :
    (PolynomialOperations.applyMatrix f A)^[j] v ≠ 0 := by
  rw [applyMatrix_iterate_eq_pow_mulVec K hops A f v j]
  intro hz
  have hb := vectorRank_bounds K A f v hv (show v ∈ powerKernel K A f j from hz)
  omega

/-- The bounded residual scan in Algorithm 2 returns the exact rank and terminal
vector. In particular, its positive-rank guard cannot drop a nonzero residual. -/
theorem residualRankSearch_correct
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n k : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Vec K n)
    (hv : v ≠ 0) (hk : v ∈ powerKernel K A f k) :
    (Id.run do
      let F := PolynomialOperations.applyMatrix f A
      let mut rank : ℕ := 0
      let mut terminal := v
      let mut w := v
      for j in List.range k do
        if rank = 0 then
          let next := F w
          if next = 0 then
            rank := j + 1
            terminal := w
          else
            w := next
      return (rank, terminal, w)) =
      (vectorRank K A f v, terminalVector K A f v, terminalVector K A f v) := by
  have hb := vectorRank_bounds K A f v hv hk
  have hc : (PolynomialOperations.applyMatrix f A)^[vectorRank K A f v] v = 0 := by
    rw [applyMatrix_iterate_eq_pow_mulVec K hops A f v]
    exact mem_powerKernel_vectorRank K A f v hk
  simpa only [applyMatrix_iterate_eq_pow_mulVec K hops A f v, terminalVector] using
    boundedRankSearch_correct (PolynomialOperations.applyMatrix f A) v
      (vectorRank K A f v) k hb.1 hb.2 hc
      (fun j hj => applyMatrix_iterate_ne_zero_of_lt_vectorRank K hops A f v hv hj)


theorem iterate_loop_eq {α : Type} (F : α → α) (v : α) (k : ℕ) :
    (Id.run do
      let mut w := v
      for _ in List.range k do
        w := F w
      return w) = F^[k] v := by
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  change (List.range k).foldl (fun b _ => F b) v = F^[k] v
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    exact (Function.iterate_succ_apply' F k v).symm

 theorem pairedLayer_loop_eq {K : Type} {n : ℕ}
    (F : Vec K n → Vec K n) (vs : List (Vec K n)) (k : ℕ) :
    (Id.run do
      let mut layer : List (PairedColumn K n) := []
      for v in vs do
        let mut top := v
        for _ in List.range k do
          top := F top
        layer := layer ++ [⟨top, v⟩]
      return layer) = vs.map (fun v => ⟨F^[k] v, v⟩) := by
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hp (v : Vec K n) : (List.range k).foldl (fun b _ => F b) v = F^[k] v := by
    have h := iterate_loop_eq F v k
    simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind] at h
    exact h
  simp only [hp]
  have hfold (xs : List (Vec K n)) (acc : List (PairedColumn K n)) :
      xs.foldl (fun b a => b ++ [⟨F^[k] a, a⟩]) acc =
        acc ++ xs.map (fun a => ⟨F^[k] a, a⟩) := by
    induction xs generalizing acc with
    | nil => simp
    | cons x xs ih => simp [ih, List.append_assoc]
  exact hfold vs []
theorem layerUpdates_fold_apply {α : Type} (layer : ℕ → α)
    (ks : List ℕ) (initial : ℕ → α) (ℓ : ℕ) :
    (ks.foldl (fun pending k => Function.update pending (k + 1) (layer (k + 1))) initial) ℓ =
      if ℓ ∈ ks.map (· + 1) then layer ℓ else initial ℓ := by
  induction ks generalizing initial with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, ih]
    by_cases h : ℓ ∈ ks.map (· + 1)
    · simp [h]
    · by_cases he : ℓ = k + 1
      · subst ℓ; simp [h]
      · simp [h, he]

/-- Initialization builds exactly the paired columns of each positive input layer. -/
theorem initializePending_loop_eq {K : Type} {n : ℕ}
    (F : Vec K n → Vec K n) (V : ℕ → List (Vec K n)) (ℓbar ℓ : ℕ) :
    (Id.run do
      let mut pending : ℕ → List (PairedColumn K n) := fun _ => []
      for k in (List.range ℓbar).reverse do
        let ℓ := k + 1
        let mut layer := []
        for v in V ℓ do
          let mut top := v
          for _ in List.range k do
            top := F top
          layer := layer ++ [⟨top, v⟩]
        pending := Function.update pending ℓ layer
      return pending) ℓ =
        if 1 ≤ ℓ ∧ ℓ ≤ ℓbar then
          (V ℓ).map (fun v => ⟨F^[ℓ - 1] v, v⟩) else [] := by
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hpair (k : ℕ) := pairedLayer_loop_eq F (V (k + 1)) k
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind] at hpair
  simp only [show ∀ k, (List.foldl
      (fun b a => b ++ [PairedColumn.mk
        ((List.range k).foldl (fun b _ => F b) a) a]) [] (V (k + 1))) =
          (V (k + 1)).map (fun v => ⟨F^[k] v, v⟩) from hpair]
  have h := layerUpdates_fold_apply
    (fun ℓ => (V ℓ).map (fun v => (⟨F^[ℓ - 1] v, v⟩ : PairedColumn K n)))
    (List.range ℓbar).reverse (fun _ => []) ℓ
  simp only [Nat.add_sub_cancel] at h
  refine h.trans ?_
  congr 1
  simp only [List.mem_map, List.mem_reverse, List.mem_range]
  apply propext
  constructor
  · rintro ⟨a, ha, he⟩; omega
  · intro h
    exact ⟨ℓ - 1, by omega, by omega⟩


theorem insertKrylovColumns_fold_invariant
    {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (F : Module.End K (Vec K n))
    (W : Submodule K (Vec K n))
    (hcomm : ∀ x, F (A *ᵥ x) = A *ᵥ F x)
    (hstable : ∀ x ∈ W, A *ᵥ x ∈ W)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hech : PairedEchelon D.toList)
    (hD : ∀ iw ∈ D.toList, iw.2.top = F iw.2.bottom)
    (hDW : ∀ iw ∈ D.toList, iw.2.bottom ∈ W)
    (hv : v.top = F v.bottom) (hvW : v.bottom ∈ W) (ks : List ℕ) :
    let out := ks.foldl
      (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
        (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩)) (D, v)
    PairedEchelon out.1.toList ∧
      (∀ iw ∈ out.1.toList, iw.2.top = F iw.2.bottom) ∧
      (∀ iw ∈ out.1.toList, iw.2.bottom ∈ W) ∧
      out.2.top = F out.2.bottom ∧ out.2.bottom ∈ W := by
  induction ks generalizing D v with
  | nil => exact ⟨hech, hD, hDW, hv, hvW⟩
  | cons j ks ih =>
    apply ih
    · exact insertPairedColumn_echelon D hech v
    · exact insertPairedColumn_top_eq F D v hD hv
    · exact insertPairedColumn_bottom_mem W D v hDW hvW
    · dsimp
      rw [hcomm, hv]
    · exact hstable v.bottom hvW

 theorem insertKrylovColumns_loop_invariant
    {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (F : Module.End K (Vec K n))
    (W : Submodule K (Vec K n))
    (hcomm : ∀ x, F (A *ᵥ x) = A *ᵥ F x)
    (hstable : ∀ x ∈ W, A *ᵥ x ∈ W)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n)
    (hech : PairedEchelon D.toList)
    (hD : ∀ iw ∈ D.toList, iw.2.top = F iw.2.bottom)
    (hDW : ∀ iw ∈ D.toList, iw.2.bottom ∈ W)
    (hv : v.top = F v.bottom) (hvW : v.bottom ∈ W) (d : ℕ) :
    let out := Id.run do
      let mut D := D
      let mut w := v
      for _ in List.range d do
        D := insertPairedColumn D w
        w := ⟨A *ᵥ w.top, A *ᵥ w.bottom⟩
      return (D, w)
    PairedEchelon out.1.toList ∧
      (∀ iw ∈ out.1.toList, iw.2.top = F iw.2.bottom) ∧
      (∀ iw ∈ out.1.toList, iw.2.bottom ∈ W) ∧
      out.2.top = F out.2.bottom ∧ out.2.bottom ∈ W := by
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  exact insertKrylovColumns_fold_invariant A F W hcomm hstable D v hech hD hDW hv hvW _
theorem truncatedKrylovSpace_succ (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (v : Vec K n) (d : ℕ) :
    truncatedKrylovSpace K A v (d + 1) =
      truncatedKrylovSpace K A v d ⊔ Submodule.span K {A^d *ᵥ v} := by
  unfold truncatedKrylovSpace
  rw [← Submodule.span_union]
  congr 1
  ext x
  simp only [mem_krylovVectors, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : j < d
    · exact Or.inl ⟨j, h, rfl⟩
    · have : j = d := by omega
      exact Or.inr (by rw [this])
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨d, by omega, rfl⟩

theorem insertKrylovColumns_fold_span
    (K : Subfield ℂ) [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) (d : ℕ) :
    let out := (List.range d).foldl
      (fun (s : Array (Fin n × PairedColumn K n) × PairedColumn K n) _ =>
        (insertPairedColumn s.1 s.2, ⟨A *ᵥ s.2.top, A *ᵥ s.2.bottom⟩)) (D, v)
    pairedTopSpan out.1 = pairedTopSpan D ⊔ truncatedKrylovSpace K A v.top d ∧
      out.2.top = A^d *ᵥ v.top ∧ out.2.bottom = A^d *ᵥ v.bottom := by
  induction d with
  | zero => simp [truncatedKrylovSpace, krylovVectors]
  | succ d ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    dsimp only at ih ⊢
    rw [pairedTopSpan_insertPairedColumn, ih.1, ih.2.1, ih.2.2,
      truncatedKrylovSpace_succ, sup_assoc]
    constructor
    · rfl
    · constructor <;> rw [pow_succ', Matrix.mulVec_mulVec]

/-- The Krylov-column loop adjoins exactly the truncated upper Krylov space. -/
theorem insertKrylovColumns_loop_span
    (K : Subfield ℂ) [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (D : Array (Fin n × PairedColumn K n)) (v : PairedColumn K n) (d : ℕ) :
    let out := Id.run do
      let mut D := D
      let mut w := v
      for _ in List.range d do
        D := insertPairedColumn D w
        w := ⟨A *ᵥ w.top, A *ᵥ w.bottom⟩
      return (D, w)
    pairedTopSpan out.1 = pairedTopSpan D ⊔ truncatedKrylovSpace K A v.top d ∧
      out.2.top = A^d *ᵥ v.top ∧ out.2.bottom = A^d *ᵥ v.bottom := by
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  exact insertKrylovColumns_fold_span K A D v d

/-- A terminal vector needs only degree(f) Krylov columns to span its cyclic space. -/
theorem truncatedKrylovSpace_eq_of_annihilated
    (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hm : f.Monic) (v : Vec K n) (hv : aeval A f *ᵥ v = 0) :
    truncatedKrylovSpace K A v f.natDegree = krylovSpace K A v := by
  have h := krylovSpace_eq_sup K A f hm v
  simpa only [hv, krylovSpace_zero, sup_bot_eq] using h.symm


/-- Under the input contract, Algorithm 2's highest-layer early return is a basis. -/
theorem algorithmInput_early_return
    (K : Subfield ℂ) {n ℓbar m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (V : ℕ → List (Vec K n))
    (hf : Irreducible f) (hm : f.Monic)
    (hmultiplicity : m = multiplicity f A.charpoly)
    (hgenerating : IsKrylovGeneratingSet K A (powerKernel K A f ℓbar)
      (algorithmInputSet V ℓbar))
    (hranks : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓbar → ∀ v ∈ V ℓ, vectorRank K A f v = ℓ)
    (hpos : 1 ≤ ℓbar) (hearly : ℓbar = m) {v : Vec K n} (hv : v ∈ V ℓbar) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) {v} := by
  apply singleton_isJordanKrylovBasis_of_rank_eq_charpoly_multiplicity
    K A f hf hm v
    (algorithmInput_ne_zero K A f V hranks hpos le_rfl hv) (algorithmInput_mem_powerKernel K A f V hgenerating hpos le_rfl hv)
  exact (hranks ℓbar hpos le_rfl v hv).trans (hearly.trans hmultiplicity)

/-- The coefficient-support bound used by the executable loop is the polynomial degree. -/
theorem coefficientSupport_sup_eq_natDegree {K : Type*} [Field K] (f : K[X]) :
    f.toFinsupp.coeff.support.sup id = f.natDegree := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact Polynomial.le_natDegree_of_mem_supp j hj
  · by_cases hz : f = 0
    · simp [hz]
    · exact Finset.le_sup (f := id) (Polynomial.natDegree_mem_support_of_nonzero hz)

/-- The end-of-layer update retains terminal columns and lowers the lower-block
kernel bound and the exponent in the paired-column relation by one. -/
theorem lowerPairedTable_invariant
    (K : Subfield ℂ) [PolynomialOperations K] {n k : ℕ}
    (hops : PolynomialOperations.IsCorrect (K := K))
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hk : 1 ≤ k)
    (D : Array (Fin n × PairedColumn K n))
    (hech : PairedEchelon D.toList)
    (hD : ∀ iw ∈ D.toList, iw.2.top = (aeval A f)^k *ᵥ iw.2.bottom)
    (hker : ∀ iw ∈ D.toList, iw.2.bottom ∈ powerKernel K A f (k + 1)) :
    let out := D.map (fun (i, w) => (i, (⟨w.top,
      PolynomialOperations.applyMatrix f A w.bottom⟩ : PairedColumn K n)))
    PairedEchelon out.toList ∧ pairedTopSpan out = pairedTopSpan D ∧
      (∀ iw ∈ out.toList, iw.2.top = (aeval A f)^(k - 1) *ᵥ iw.2.bottom) ∧
      (∀ iw ∈ out.toList, iw.2.bottom ∈ powerKernel K A f k) := by
  dsimp only
  refine ⟨?_, pairedTopSpan_map_bottom D _, ?_, ?_⟩
  · simpa only [Array.toList_map] using
      hech.map_bottom D.toList (PolynomialOperations.applyMatrix f A)
  · intro iw hiw
    obtain ⟨jw, hjw, rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using hiw)
    dsimp only
    rw [hops.applyMatrix_eq, Matrix.mulVec_mulVec, ← pow_succ,
      Nat.sub_add_cancel hk]
    exact hD jw hjw
  · intro iw hiw
    obtain ⟨jw, hjw, rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using hiw)
    change (aeval A f)^k *ᵥ PolynomialOperations.applyMatrix f A jw.2.bottom = 0
    rw [hops.applyMatrix_eq, Matrix.mulVec_mulVec, ← pow_succ]
    exact hker jw hjw

end SympyProofs.JordanKrylov
