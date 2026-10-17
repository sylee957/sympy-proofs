import SympyProofs.JordanKrylov.Algorithms.PrimaryGenerating
import SympyProofs.JordanKrylov.Mathematics.RankPartition
import Std.Tactic.Do
import Std.WP

/-! # Supporting lemmas for primary generator computation

Loop semantics, cofactor properties, rank layers, and the bridge to Algorithm 2.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Proof-only rank-level model of primary generator construction. -/
def primaryGeneratorsModel (K : Type*) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (p : Fin m → K[X]) (ranks : Fin m → ℕ) :
    ℕ → List (Fin n → K) := Id.run do
  let maxRank := Finset.univ.sup (fun i : Fin m => ranks i)
  let mut generators : ℕ → List (Fin n → K) := fun _ => []
  for k in (List.range maxRank).reverse do
    let ℓ := k + 1
    let mut layer := []
    for i in List.finRange m do
      if 0 < ℓ ∧ ranks i = ℓ then
        let divisor := Operations.pow f (ranks i)
        let cofactor := Operations.divMonic divisor (p i)
        let vector := Operations.applyMatrix cofactor A (e i)
        layer := layer ++ [vector]
    generators := Function.update generators ℓ layer
  return generators

open scoped Std.WP in
private theorem maximumRanks_eq {m : ℕ} (ranks : Fin m → ℕ) :
    (Id.run do
      let mut bound := 0
      for i in List.finRange m do
        bound := max bound (ranks i)
      return bound) = Finset.univ.sup ranks := by
  generalize h : Id.run _ = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ bound => bound = pref.toFinset.sup ranks
  case vc1 => simp
  case vc2 => simp_all
  case vc3 => simp_all [bound, Finset.sup_insert, max_comm]

/-- The routine agrees with the rank-level proof model and returns
its maximum rank from the same input data. -/
theorem computePrimaryGenerators_eq_model
    (K : Type) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (f : K[X])
    (polynomials : Vector K[X] m)
    (ranks : Vector ℕ m) :
    computePrimaryGenerators K A e f polynomials ranks =
      (primaryGeneratorsModel K A e f
        (fun i : Fin m => polynomials[i]) (fun i : Fin m => ranks[i]),
        Finset.univ.sup (fun i : Fin m => ranks[i])) := by
  have hmax := maximumRanks_eq (fun i : Fin m => ranks[i])
  simp only [List.forIn_pure_yield_eq_foldl] at hmax
  change (List.finRange m).foldl (fun bound i => max bound (ranks[i])) 0 = _ at hmax
  simp only [computePrimaryGenerators, primaryGeneratorsModel,
    List.forIn_pure_yield_eq_foldl]
  rw [hmax]
  rfl

private theorem foldl_append_filter {ι V : Type*}
    (ks : List ι) (pred : ι → Prop) [DecidablePred pred] (w : ι → V) (s : List V) :
    ks.foldl (fun acc i => if pred i then acc ++ [w i] else acc) s =
      s ++ (ks.filter pred).map w := by
  induction ks generalizing s with
  | nil => simp
  | cons i ks ih =>
    by_cases hi : pred i <;> simp [List.foldl_cons, hi, ih, List.append_assoc]

private theorem forIn_append_filter {ι V : Type*}
    (ks : List ι) (pred : ι → Prop) [DecidablePred pred] (w : ι → V) :
    (forIn ks ([] : List V)
      (fun i s => if pred i then pure (ForInStep.yield (s ++ [w i])) else
        pure (ForInStep.yield s)) : Id (List V)) =
      pure ((ks.filter pred).map w) := by
  have hbody (i : ι) (s : List V) :
      (if pred i then pure (ForInStep.yield (s ++ [w i])) else
        pure (ForInStep.yield s) : Id (ForInStep (List V))) =
      pure (ForInStep.yield (if pred i then s ++ [w i] else s)) := by
    split <;> rfl
  simp only [hbody, List.forIn_pure_yield_eq_foldl]
  simp [foldl_append_filter]

private theorem foldl_store_layers {V : Type*} (ks : List ℕ)
    (layer s : ℕ → List V) (ℓ : ℕ) :
    (ks.foldl (fun acc k => Function.update acc (k + 1) (layer (k + 1))) s) ℓ =
      if ∃ k ∈ ks, k + 1 = ℓ then layer ℓ else s ℓ := by
  induction ks generalizing s with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, ih]
    by_cases h : ∃ j ∈ ks, j + 1 = ℓ
    · simp [h]
    · by_cases hk : k + 1 = ℓ
      · subst ℓ
        simp
      · simp [h, hk, Ne.symm hk]

/-- Membership in a returned list is exactly membership in its mathematical layer. -/
theorem mem_primaryGeneratorsModel (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (_hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (_hp : ∀ i, p i ≠ 0) (ℓ : ℕ) (v : Fin n → K) :
    v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ ↔
      v ∈ primaryGeneratorLayer K A e f p ℓ := by
  classical
  let L := Finset.univ.sup (fun i => multiplicity f (p i))
  let layer := fun ℓ => ((List.finRange m).filter
    (fun i => 0 < ℓ ∧ multiplicity f (p i) = ℓ)).map
      (fun i => aeval A (primaryCofactor K f (p i)) *ᵥ e i)
  have hmem (j : ℕ) : v ∈ layer j ↔ v ∈ primaryGeneratorLayer K A e f p j := by
    simp [layer, primaryGeneratorLayer]
  have hbound : v ∈ primaryGeneratorLayer K A e f p ℓ → 1 ≤ ℓ ∧ ℓ ≤ L := by
    intro hv
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hv
    have hi := (Finset.mem_filter.mp hi).2
    exact ⟨hi.1, hi.2 ▸ Finset.le_sup (f := fun i => multiplicity f (p i)) (Finset.mem_univ i)⟩
  unfold primaryGeneratorsModel
  simp only [hops.pow_eq, hops.divMonic_eq _ _ (hm.pow _),
    Polynomial.divByMonic_eq_div _ (hm.pow _), hops.applyMatrix_eq,
    forIn_append_filter, pure_bind, List.forIn_pure_yield_eq_foldl]
  change (v ∈ ((List.range L).reverse.foldl
    (fun s k => Function.update s (k + 1) (layer (k + 1))) (fun _ => []) ℓ)) ↔ _
  rw [foldl_store_layers]
  have hex : (∃ k ∈ (List.range L).reverse, k + 1 = ℓ) ↔ 1 ≤ ℓ ∧ ℓ ≤ L := by
    simp only [List.mem_reverse, List.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨hpos, hle⟩
      exact ⟨ℓ - 1, by omega, by omega⟩
  simp only [hex]
  split
  · exact hmem ℓ
  · rename_i h
    simp only [List.not_mem_nil, false_iff]
    exact fun hv => h (hbound hv)

/-- The union of the output layers is exactly the cofactor generating set. -/
theorem primaryGeneratorsModel_eq (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i ≠ 0) :
    {v | ∃ ℓ, v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ} =
      primaryGeneratingSet K A e (fun i => multiplicity f (p i))
        (fun i => primaryCofactor K f (p i)) := by
  classical
  ext v
  simp only [Set.mem_ofPred_eq,
    mem_primaryGeneratorsModel K hops A e f hf hm p hp,
    primaryGeneratorLayer, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, primaryGeneratingSet, Set.mem_image,
    primaryBasisIndices]
  constructor
  · rintro ⟨ℓ, i, ⟨hpos, hi⟩, hv⟩
    exact ⟨i, by omega, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨multiplicity f (p i), i, ⟨hi, rfl⟩, hv⟩

/-- The bounded input for Algorithm 2 equals the union of all output layers. -/
theorem primaryGeneratorsModel_inputSet_eq (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i ≠ 0)
    (hbound : ∀ i, multiplicity f (p i) ≤ ℓbar) :
    algorithmInputSet (primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i))) ℓbar =
      {v | ∃ ℓ, v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ} := by
  ext v
  simp only [algorithmInputSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ℓ, _, _, hv⟩
    exact ⟨ℓ, hv⟩
  · rintro ⟨ℓ, hv⟩
    have hlayer := (mem_primaryGeneratorsModel K hops A e f hf hm p hp ℓ v).mp hv
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hlayer
    obtain ⟨hpos, hi⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨ℓ, hpos, hi ▸ hbound i, hv⟩

/-- Division by the full power is exact. -/
theorem primaryCofactor_factorization (K : Subfield ℂ) (f p : K[X]) (hf : f ≠ 0) :
    p = f ^ multiplicity f p * primaryCofactor K f p := by
  exact (EuclideanDomain.mul_div_cancel' (pow_ne_zero _ hf)
    (pow_multiplicity_dvd f p)).symm

/-- The cofactor vector has exactly the exponent removed from its annihilator. -/
theorem vectorRank_primaryCofactor (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) :
    vectorRank K A f (aeval A (primaryCofactor K f
      (minimalAnnihilatingPolynomial K A u)) *ᵥ u) =
      multiplicity f (minimalAnnihilatingPolynomial K A u) := by
  let p := minimalAnnihilatingPolynomial K A u
  let m := multiplicity f p
  let g := primaryCofactor K f p
  have hfac : p = f ^ m * g := primaryCofactor_factorization K f p hf.ne_zero
  have hker := cofactorVector_mem_powerKernel K A f u m g hfac
  change vectorRank K A f (aeval A g *ᵥ u) = m
  by_cases hm : m = 0
  · have hz : aeval A g *ᵥ u = 0 := by simpa [hm] using hker
    simp [hz, hm]
  · apply (vectorRank_eq_iff K A f _ hker (by omega)).mpr
    refine ⟨hker, ?_⟩
    intro hprev
    have hd : p ∣ f ^ (m - 1) * g := by
      apply (minimalAnnihilatingPolynomial_dvd_iff K A u _).mpr
      simpa only [map_mul, map_pow, ← Matrix.mulVec_mulVec] using
        (mem_powerKernel K A f (m - 1) _).mp hprev
    have hg : g ≠ 0 := by
      intro hz
      have hp0 : p = 0 := by simpa [hz] using hfac
      exact (minimalAnnihilatingPolynomial_monic K A u).ne_zero hp0
    rw [hfac, mul_dvd_mul_iff_right hg] at hd
    have := (pow_dvd_pow_iff hf.ne_zero hf.not_isUnit).mp hd
    omega

/-- Remark 2: each positive layer is exactly the rank-ℓ part of the returned set. -/
theorem primaryGeneratorLayer_eq_rankSubset (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (primaryGeneratorLayer K A e f p ℓ : Set (Fin n → K)) =
      rankSubset K A f {v | ∃ ℓ, v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ} ℓ := by
  classical
  rw [primaryGeneratorsModel_eq K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)]
  ext v
  simp only [primaryGeneratorLayer, Finset.mem_coe, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, rankSubset,
    primaryGeneratingSet, primaryBasisIndices, Set.mem_ofPred_eq, Set.mem_image]
  have hr (i : Fin m) : vectorRank K A f (aeval A (primaryCofactor K f (p i)) *ᵥ e i) =
      multiplicity f (p i) := by
    rw [hp i]
    exact vectorRank_primaryCofactor K A f hf (e i)
  constructor
  · rintro ⟨i, ⟨_, hi⟩, rfl⟩
    exact ⟨⟨i, by omega, rfl⟩, (hr i).trans hi⟩
  · rintro ⟨⟨i, hi, rfl⟩, hv⟩
    exact ⟨i, ⟨hℓ, (hr i).symm.trans hv⟩, rfl⟩

end SympyProofs.JordanKrylov
