import SympyProofs.JordanKrylov.Algorithms.JordanChains
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisLemmas

namespace SympyProofs.JordanKrylov
open Matrix Polynomial
universe u

private theorem forIn_rcc {β : Type} (a b : ℕ) (init : β)
    (step : ℕ → β → Id (ForInStep β)) :
    forIn (a...=b) init step = forIn (a...=b).toList init step := by
  change forIn' (a...=b) init (fun k _ s => step k s) = _
  rw [Std.Rcc.forIn'_eq_forIn'_toList]
  rfl

private theorem forIn_rco {β : Type} (n : ℕ) (init : β)
    (step : ℕ → β → Id (ForInStep β)) :
    forIn (0...n) init step = forIn (List.range n) init step := by
  change forIn' (0...n) init (fun k _ s => step k s) = _
  rw [Std.Rco.forIn'_eq_forIn'_toList, ← List.range_eq_toList_rco]
  rfl

private theorem descending_layers (n : ℕ) :
    (List.range n).map (fun i => n - i) = (List.range n).reverse.map Nat.succ := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp [List.getElem_reverse]
    omega

private theorem descending_entries (n : ℕ) :
    (List.range (n - 1)).map (fun i => n - i) =
      (List.range (n - 1)).reverse.map (· + 2) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp [List.getElem_reverse]
    omega

/-- Recursive proof model of a single descending chain. -/
def jordanChainModel {V P : Type u} (F : V → V) (Q : ℕ → V → P) : ℕ → V → List P
  | 0, _ => []
  | k + 1, b => Q (k + 1) b :: jordanChainModel F Q k (F b)

private theorem chain_fold {V P : Type u} (F : V → V) (Q : ℕ → V → P)
    (ℓ : ℕ) (acc : List P) (b : V) :
    let out := ((List.range ℓ).reverse.map (· + 2)).foldl
      (fun (s : List P × V) k => (s.1 ++ [Q k s.2], F s.2)) (acc, b)
    out.1 ++ [Q 1 out.2] = acc ++ jordanChainModel F Q (ℓ + 1) b := by
  induction ℓ generalizing acc b with
  | zero => simp [jordanChainModel]
  | succ k ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.foldl_cons]
    rw [ih]
    simp [jordanChainModel, List.append_assoc]

theorem jordanChain_loop_eq_model {V P : Type} (F : V → V) (Q : ℕ → V → P)
    (ℓ : ℕ) (b : V) :
    (Id.run do
      let mut chain := []
      let mut current := b
      for offset in 0...(ℓ - 1) do
        chain := chain ++ [Q (ℓ - offset) current]
        current := F current
      chain := chain ++ [Q 1 current]
      return chain) = jordanChainModel F Q (ℓ - 1 + 1) b := by
  simp only [forIn_rco, List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  have hmap := descending_entries ℓ
  have hfold := congrArg (fun xs => xs.foldl
    (fun (s : List P × V) k => (s.1 ++ [Q k s.2], F s.2)) ([], b)) hmap
  simp only [List.foldl_map] at hfold
  rw [hfold]
  simpa only [List.nil_append, Pure.pure, List.foldl_map] using chain_fold F Q (ℓ - 1) [] b

theorem jordanChainModel_eq_ofFn {V P : Type u} (F : V → V) (Q : ℕ → V → P)
    (ℓ : ℕ) (b : V) :
    jordanChainModel F Q ℓ b =
      List.ofFn (fun j : Fin ℓ => Q (ℓ - j.val) (F^[j.val] b)) := by
  induction ℓ generalizing b with
  | zero => simp [jordanChainModel]
  | succ k ih =>
    rw [jordanChainModel, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Function.iterate_zero, id_eq]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext j
    simp [Function.iterate_succ_apply]

/-- Proof model of the precomputed polynomial action. -/
def chainPowerAction (K : Type) [Field K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓbar k : ℕ) (v : Fin n → K) :=
  let zeroPower := PolynomialOperations.reducedPower f 0
  let powers := Id.run do
    let mut powers := #[zeroPower]
    for j in 1...=ℓbar do
      powers := powers.push (PolynomialOperations.reducedPower f j)
    return powers
  PolynomialOperations.applyBivariateMatrix (powers[k]?.getD zeroPower) A v

theorem chainPowerAction_eq
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar k : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Fin n → K) (hk : k ≤ ℓbar) :
    chainPowerAction K A f ℓbar k v =
      (ψPower K f k).eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ (fun i => C (v i)) := by
  cases k with
  | zero =>
    simp [chainPowerAction, forIn_rcc, Nat.toList_rcc_eq_toList_rco,
      Nat.toList_rco_succ_succ, ← List.range_eq_toList_rco, List.forIn_pure_yield_eq_foldl,
      hops.reducedPower_eq K, hops.applyBivariateMatrix_eq]
  | succ k =>
    have hk' : k < ℓbar := by omega
    simp [chainPowerAction, forIn_rcc, Nat.toList_rcc_eq_toList_rco,
      Nat.toList_rco_succ_succ, ← List.range_eq_toList_rco, List.forIn_pure_yield_eq_foldl, hk',
      hops.reducedPower_eq K, hops.applyBivariateMatrix_eq]

/-- The computed chain is precisely the paper's polynomial-coordinate formula. -/
theorem jordanChainModel_eq_coordinates
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar ℓ : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (b : Fin n → K) (hle : ℓ ≤ ℓbar) :
    jordanChainModel (PolynomialOperations.applyMatrix f A) (chainPowerAction K A f ℓbar) ℓ b =
      List.ofFn (fun j : Fin ℓ => pChainCoordinates K A f ℓ (ℓ - j.val) b) := by
  rw [jordanChainModel_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [chainPowerAction_eq K hops A f _ (by omega),
    applyMatrix_iterate_eq_pow_mulVec K hops A f b]
  simp only [pChainCoordinates, Nat.sub_sub_self (Nat.le_of_lt j.isLt)]

private theorem insert_fold_eq_union {α β : Type*} [DecidableEq β]
    (xs : List α) (g : α → β) (acc : Finset β) :
    xs.foldl (fun out b => insert (g b) out) acc = acc ∪ (xs.map g).toFinset := by
  induction xs generalizing acc with
  | nil => simp
  | cons b xs ih => simp [List.foldl_cons, ih, Finset.insert_union]

private theorem mem_union_fold {α : Type*} [DecidableEq α] (xs : List ℕ)
    (B : ℕ → Finset α) (acc : Finset α) (c : α) :
    c ∈ xs.foldl (fun out j => out ∪ B j) acc ↔
      c ∈ acc ∨ ∃ j ∈ xs, c ∈ B j := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih => simp [List.foldl_cons, ih, or_assoc]

private theorem array_getElem_eq_getD {α : Type*} (fallback : α)
    (xs : Array α) (i : ℕ) (h : i < xs.size) :
    xs[i] = xs[i]?.getD fallback := by
  simp [h]

/-- Exact coverage of the assembly loop, before replacing operations by their specifications. -/
theorem mem_computeJordanChains
    (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ) (c : List (Fin n → K[X])) :
    c ∈ computeJordanChains K A f B ℓbar ↔
      ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ ℓbar ∧ ∃ b ∈ B ℓ,
        jordanChainModel (PolynomialOperations.applyMatrix f A)
          (chainPowerAction K A f ℓbar) ℓ b = c := by
  let loop := fun ℓ b => Id.run do
    let mut chain := []
    let mut current := b
    for offset in 0...(ℓ - 1) do
      chain := chain ++ [chainPowerAction K A f ℓbar (ℓ - offset) current]
      current := PolynomialOperations.applyMatrix f A current
    chain := chain ++ [chainPowerAction K A f ℓbar 1 current]
    return chain
  have heq : loop = fun ℓ => jordanChainModel (PolynomialOperations.applyMatrix f A)
      (chainPowerAction K A f ℓbar) (ℓ - 1 + 1) := by
    funext ℓ b
    exact jordanChain_loop_eq_model _ _ ℓ b
  simp only [computeJordanChains,
    array_getElem_eq_getD (PolynomialOperations.reducedPower f 0)]
  change c ∈ Id.run (forIn (0...ℓbar) ∅ (fun offset out => do
    let out ← forIn (B (ℓbar - offset)) out
      (fun b out => pure (ForInStep.yield (insert (loop (ℓbar - offset) b) out)))
    pure (ForInStep.yield out)) : Id (Finset (List (Fin n → K[X])))) ↔ _
  rw [forIn_rco]
  have houter := List.forIn_map (m := Id) (l := List.range ℓbar)
    (g := fun offset => ℓbar - offset) (init := (∅ : Finset (List (Fin n → K[X]))))
    (f := fun ℓ out => do
      let out ← forIn (B ℓ) out
        (fun b out => pure (ForInStep.yield (insert (loop ℓ b) out)))
      pure (ForInStep.yield out))
  rw [← houter, descending_layers]
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run]
  change c ∈ ((List.range ℓbar).reverse.map Nat.succ).foldl
    (fun out j => (B j).foldl (fun out b => insert (loop j b) out) out) (∅ : Finset (List (Fin n → K[X]))) ↔ _
  rw [heq]
  simp_rw [insert_fold_eq_union]
  rw [mem_union_fold]
  simp only [Finset.notMem_empty, false_or, List.mem_map, List.mem_reverse,
    List.mem_range, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, b, hb, he⟩
    exact ⟨k+1, by omega, by omega, b, hb, by simpa using he⟩
  · rintro ⟨j, hp, hl, b, hb, he⟩
    exact ⟨j, ⟨j-1, by omega, by omega⟩, b, hb, by simpa [Nat.sub_add_cancel hp] using he⟩

/-- Every returned chain is the formula for an input generator, and every input
generator in the processed layers contributes its chain. -/
theorem mem_computeJordanChains_iff
    (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ) (c : List (Fin n → K[X])) :
    c ∈ computeJordanChains K A f B ℓbar ↔
      ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ ℓbar ∧ ∃ b ∈ B ℓ,
        List.ofFn (fun j : Fin ℓ => pChainCoordinates K A f ℓ (ℓ - j.val) b) = c := by
  rw [mem_computeJordanChains]
  constructor <;> rintro ⟨ℓ, hp, hl, b, hb, he⟩ <;> refine ⟨ℓ, hp, hl, b, hb, ?_⟩
  · rwa [jordanChainModel_eq_coordinates K hops A f b hl] at he
  · rwa [jordanChainModel_eq_coordinates K hops A f b hl]


end SympyProofs.JordanKrylov
