import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations
import SympyProofs.JordanKrylov.Mathematics.PrimaryGeneratingSet
import SympyProofs.JordanKrylov.Mathematics.RankPartition

/-! # Computing primary Krylov generators

Algorithm 1 in imperative form. The vector annihilating polynomials are inputs.
The algorithm runs over a field with decidable equality, using supplied
polynomial operations. The correctness theorems specialize
to the existing subfield-of-ℂ theory.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- The cofactor computed by exact polynomial division in Algorithm 1. -/
noncomputable def primaryCofactor (K : Subfield ℂ) (f p : K[X]) : K[X] :=
  p / f ^ multiplicity f p

/-- The layer `𝓥^(ℓ)` computed in one iteration. The zero layer is empty. -/
noncomputable def primaryGeneratorLayer (K : Subfield ℂ) [DecidableEq K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (f : K[X]) (p : Fin m → K[X]) (ℓ : ℕ) : Finset (Fin n → K) :=
  (Finset.univ.filter (fun i => 0 < ℓ ∧ multiplicity f (p i) = ℓ)).image
    (fun i => aeval A (primaryCofactor K f (p i)) *ᵥ e i)

/-- Algorithm 1: compute the maximum multiplicity, process ranks in descending
order, and return the union of their cofactor vectors. The input indices are
visited in increasing order inside each layer. -/
def computePrimaryGenerators (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (p : Fin m → K[X]) :
    Finset (Fin n → K) := Id.run do
  let ranks := fun i => PolynomialOperations.multiplicity f (p i)
  let maxRank := Finset.univ.sup ranks
  let mut generators := ∅
  for k in (List.range maxRank).reverse do
    let ℓ := k + 1
    let mut layer := ∅
    for i in List.finRange m do
      if 0 < ℓ ∧ ranks i = ℓ then
        let divisor := PolynomialOperations.pow f (ranks i)
        let cofactor := PolynomialOperations.divMonic divisor (p i)
        let vector := PolynomialOperations.applyMatrix cofactor A (e i)
        layer := insert vector layer
    generators := generators ∪ layer
  return generators

private theorem foldl_insert_filter {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (ks : List ι) (pred : ι → Prop) [DecidablePred pred] (w : ι → V) (s : Finset V) :
    ks.foldl (fun acc i => if pred i then insert (w i) acc else acc) s =
      s ∪ (ks.toFinset.filter pred).image w := by
  induction ks generalizing s with
  | nil => simp
  | cons i ks ih =>
    by_cases hi : pred i
    · simp [List.foldl_cons, hi, ih, Finset.filter_insert, Finset.insert_union,
        Finset.union_insert]
    · simp [List.foldl_cons, hi, ih, Finset.filter_insert]

private theorem forIn_insert_filter {ι V : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq V]
    (pred : ι → Prop) [DecidablePred pred] (w : ι → V) :
    (forIn (Finset.univ.sort (· ≤ ·)) (∅ : Finset V)
      (fun i s => if pred i then pure (ForInStep.yield (insert (w i) s)) else
        pure (ForInStep.yield s)) : Id (Finset V)) =
      pure ((Finset.univ.filter pred).image w) := by
  have hbody (i : ι) (s : Finset V) :
      (if pred i then pure (ForInStep.yield (insert (w i) s)) else
        pure (ForInStep.yield s) : Id (ForInStep (Finset V))) =
      pure (ForInStep.yield (if pred i then insert (w i) s else s)) := by
    split <;> rfl
  simp only [hbody, List.forIn_pure_yield_eq_foldl]
  change pure ((Finset.univ.sort (· ≤ ·)).foldl
    (fun s i => if pred i then insert (w i) s else s) ∅) = _
  simp [foldl_insert_filter]

private theorem mem_foldl_union {V : Type*} [DecidableEq V]
    (layer : ℕ → Finset V) (ks : List ℕ) (s : Finset V) (v : V) :
    v ∈ ks.foldl (fun acc k => acc ∪ layer (k + 1)) s ↔
      v ∈ s ∨ ∃ k ∈ ks, v ∈ layer (k + 1) := by
  induction ks generalizing s with
  | nil => simp
  | cons k ks ih => simp [List.foldl_cons, ih, or_assoc]

/-- Membership in the algorithm's output is membership in a positive layer. -/
theorem mem_computePrimaryGenerators (K : Subfield ℂ) [DecidableEq K]
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect (K := K)) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i ≠ 0) (v : Fin n → K) :
    v ∈ computePrimaryGenerators K A e f p ↔
      ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ Finset.univ.sup (fun i => multiplicity f (p i)) ∧
        v ∈ primaryGeneratorLayer K A e f p ℓ := by
  classical
  let L := Finset.univ.sup (fun i => multiplicity f (p i))
  let layer := primaryGeneratorLayer K A e f p
  have hr (i : Fin m) := hops.multiplicity_eq f (p i)
    (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hf)) hm (hp i)
  unfold computePrimaryGenerators
  rw [← Fin.sort_univ]
  dsimp only
  simp only [hr, hops.pow_eq, hops.divMonic_eq _ _ (hm.pow _),
    Polynomial.divByMonic_eq_div _ (hm.pow _), hops.applyMatrix_eq, forIn_insert_filter, pure_bind]
  change v ∈ (forIn (List.range L).reverse (∅ : Finset (Fin n → K))
    (fun k s => pure (ForInStep.yield (s ∪ layer (k + 1)))) :
      Id (Finset (Fin n → K))).run ↔ _
  rw [List.forIn_pure_yield_eq_foldl (m := Id)]
  change v ∈ (List.range L).reverse.foldl (fun s k => s ∪ layer (k + 1)) ∅ ↔ _
  simp only [mem_foldl_union, Finset.notMem_empty, false_or, List.mem_reverse,
    List.mem_range]
  constructor
  · rintro ⟨k, hk, hv⟩
    exact ⟨k + 1, by omega, by omega, hv⟩
  · rintro ⟨ℓ, hpos, hle, hv⟩
    exact ⟨ℓ - 1, by omega, by simpa [Nat.sub_add_cancel hpos] using hv⟩

/-- The descending imperative loop returns exactly the cofactor generating set. -/
theorem computePrimaryGenerators_eq (K : Subfield ℂ) [DecidableEq K]
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect (K := K)) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i ≠ 0) :
    (computePrimaryGenerators K A e f p : Set (Fin n → K)) =
      primaryGeneratingSet K A e (fun i => multiplicity f (p i))
        (fun i => primaryCofactor K f (p i)) := by
  classical
  ext v
  change v ∈ computePrimaryGenerators K A e f p ↔ _
  rw [mem_computePrimaryGenerators K hops A e f hf hm p hp]
  simp only [primaryGeneratorLayer, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, primaryGeneratingSet, Set.mem_image,
    primaryBasisIndices, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ℓ, hpos, _, i, ⟨_, hi⟩, hv⟩
    exact ⟨i, by omega, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨multiplicity f (p i), hi,
      Finset.le_sup (f := fun j => multiplicity f (p j)) (Finset.mem_univ i),
      i, ⟨hi, rfl⟩, hv⟩

/-- Division by the full power is exact. -/
theorem primaryCofactor_factorization (K : Subfield ℂ) (f p : K[X]) (hf : f ≠ 0) :
    p = f ^ multiplicity f p * primaryCofactor K f p := by
  exact (EuclideanDomain.mul_div_cancel' (pow_ne_zero _ hf)
    (pow_multiplicity_dvd f p)).symm

/-- Algorithm 1 is correct when its polynomial inputs are a spanning family's
minimal annihilating polynomials. -/
theorem computePrimaryGenerators_correct (K : Subfield ℂ) [DecidableEq K]
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect (K := K)) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i)) :
    IsKrylovGeneratingSet K A (powerKernel K A f (multiplicity f (minpoly K A)))
      (computePrimaryGenerators K A e f p : Set (Fin n → K)) := by
  rw [computePrimaryGenerators_eq K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)]
  have hp' : p = fun i => minimalAnnihilatingPolynomial K A (e i) := funext hp
  subst p
  exact primaryGeneratingSet_isKrylovGeneratingSet_minpoly K A e he f hf hm _
    (fun i => primaryCofactor_factorization K f _ hf.ne_zero)

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
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect (K := K)) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (primaryGeneratorLayer K A e f p ℓ : Set (Fin n → K)) =
      rankSubset K A f (computePrimaryGenerators K A e f p) ℓ := by
  classical
  rw [computePrimaryGenerators_eq K hops A e f hf hm p
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
