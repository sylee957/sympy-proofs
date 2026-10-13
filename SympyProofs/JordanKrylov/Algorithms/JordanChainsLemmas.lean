import SympyProofs.JordanKrylov.Algorithms.JordanChains
import SympyProofs.JordanKrylov.Algorithms.JordanKrylovBasisLemmas

namespace SympyProofs.JordanKrylov
open Matrix Polynomial
universe u

/-- Recursive proof model of a single descending chain. -/
def jordanChainModel {V P : Type u} (F : V → V) (Q : ℕ → V → P) : ℕ → V → List P
  | 0, _ => []
  | k + 1, b => Q (k + 1) b :: jordanChainModel F Q k (F b)

private theorem chain_fold {V P : Type u} (F : V → V) (Q : ℕ → V → P)
    (ℓ : ℕ) (acc : List P) (b : V) :
    ((List.range ℓ).reverse.foldl (fun (s : List P × V) k =>
      (s.1 ++ [Q (k+1) s.2], if 0 < k then F s.2 else s.2)) (acc, b)).1 =
      acc ++ jordanChainModel F Q ℓ b := by
  induction ℓ generalizing acc b with
  | zero => simp [jordanChainModel]
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.foldl_cons]
    dsimp only
    rw [ih]
    cases k with
    | zero => simp [jordanChainModel]
    | succ k => simp [jordanChainModel, List.append_assoc]

theorem jordanChain_loop_eq_model {V P : Type u} (F : V → V) (Q : ℕ → V → P)
    (ℓ : ℕ) (b : V) :
    (Id.run do
      let mut chain := []
      let mut current := b
      for k in (List.range ℓ).reverse do
        chain := chain ++ [Q (k + 1) current]
        if 0 < k then
          current := F current
      return chain) = jordanChainModel F Q ℓ b := by
  have hy {α : Type} {β : Type u} (xs : List α) (init : β) (step : α → β → β) :
      (forIn xs init (fun a b => ForInStep.yield (step a b)) : Id β) =
        xs.foldl (fun b a => step a b) init :=
    List.forIn_pure_yield_eq_foldl (m := Id) step init
  simp only [Id.run, Bind.bind, Pure.pure, ← apply_ite]
  change ((forIn (List.range ℓ).reverse ([], b) (fun k s =>
    ForInStep.yield (s.1 ++ [Q (k+1) s.2], if 0 < k then F s.2 else s.2)) :
      Id (List P × V)).1) = _
  rw [hy]
  simpa only [List.nil_append] using chain_fold F Q ℓ [] b

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
def chainPowerAction (K : Type*) [Field K] [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓbar k : ℕ) (v : Fin n → K) :=
  let powers := Vector.ofFn (fun j : Fin (ℓbar + 1) =>
    PolynomialOperations.reducedPower f j.val)
  PolynomialOperations.applyBivariateMatrix (powers[k]?.getD powers[0]) A v

theorem chainPowerAction_eq
    (K : Subfield ℂ) [PolynomialOperations K] {n ℓbar k : ℕ}
    (hops : PolynomialOperations.IsCorrect K)
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (v : Fin n → K) (hk : k ≤ ℓbar) :
    chainPowerAction K A f ℓbar k v =
      (ψPower K f k).eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ (fun i => C (v i)) := by
  simp [chainPowerAction, show k < ℓbar + 1 by omega,
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

/-- Exact coverage of the assembly loop, before replacing operations by their specifications. -/
theorem mem_computeJordanChains
    (K : Type*) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ) (c : List (Fin n → K[X])) :
    c ∈ computeJordanChains K A f B ℓbar ↔
      ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ ℓbar ∧ ∃ b ∈ B ℓ,
        jordanChainModel (PolynomialOperations.applyMatrix f A)
          (chainPowerAction K A f ℓbar) ℓ b = c := by
  let loop := fun ℓ b => Id.run do
    let mut chain := []
    let mut current := b
    for k in (List.range ℓ).reverse do
      chain := chain ++ [chainPowerAction K A f ℓbar (k + 1) current]
      if 0 < k then
        current := PolynomialOperations.applyMatrix f A current
    return chain
  have heq : loop = jordanChainModel (PolynomialOperations.applyMatrix f A)
      (chainPowerAction K A f ℓbar) := by
    funext ℓ b
    exact jordanChain_loop_eq_model _ _ ℓ b
  change c ∈ Id.run (forIn ((List.range ℓbar).reverse.map Nat.succ) ∅ (fun ℓ out => do
    let out ← forIn (B ℓ) out (fun b out => pure (ForInStep.yield (insert (loop ℓ b) out)))
    pure (ForInStep.yield out)) : Id (Finset (List (Fin n → K[X])))) ↔ _
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
    exact ⟨k+1, by omega, by omega, b, hb, he⟩
  · rintro ⟨j, hp, hl, b, hb, he⟩
    exact ⟨j, ⟨j-1, by omega, by omega⟩, b, hb, he⟩

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
