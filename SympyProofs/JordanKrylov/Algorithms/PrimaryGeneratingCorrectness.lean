import SympyProofs.JordanKrylov.Algorithms.PrimaryGeneratingLemmas

/-! # Correctness of primary generator computation

The output generates the primary kernel, and each layer has its prescribed rank.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1 is correct when its polynomial inputs are a spanning family's
minimal annihilating polynomials. -/
theorem primaryGeneratorsModel_correct (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i)) :
    IsKrylovGeneratingSet K A (powerKernel K A f (multiplicity f (minpoly K A)))
      {v | ∃ ℓ, v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ} := by
  rw [primaryGeneratorsModel_eq K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)]
  have hp' : p = fun i => minimalAnnihilatingPolynomial K A (e i) := funext hp
  subst p
  exact primaryGeneratingSet_isKrylovGeneratingSet_minpoly K A e he f hf hm _
    (fun i => primaryCofactor_factorization K f _ hf.ne_zero)

/-- Every returned vector has the rank indexing its list. -/
theorem primaryGeneratorsModel_ranks (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (ℓ : ℕ) (v : Fin n → K) (hv : v ∈ primaryGeneratorsModel K A e f p (fun i => multiplicity f (p i)) ℓ) :
    vectorRank K A f v = ℓ := by
  rw [mem_primaryGeneratorsModel K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)] at hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  have hi := (Finset.mem_filter.mp hi).2.2
  rw [hp i] at hi ⊢
  exact (vectorRank_primaryCofactor K A f hf (e i)).trans hi

/-- The routine generates the selected primary kernel when the
inputs contain the input vectors' minimal annihilators and their exponents. -/
theorem computePrimaryGenerators_correct (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (he : Submodule.span K (Set.range e) = ⊤)
    (f : K[X]) (j : Fin q)
    (polynomials : Vector K[X] m)
    (multiplicities : Vector (Vector ℕ q) m)
    (hf : Irreducible f) (hm : f.Monic)
    (hp : ∀ i : Fin m, polynomials[i] = minimalAnnihilatingPolynomial K A (e i))
    (hr : ∀ i : Fin m, multiplicities[i][j] = multiplicity f polynomials[i]) :
    IsKrylovGeneratingSet K A
      (powerKernel K A f (multiplicity f (minpoly K A)))
      {v | ∃ ℓ, v ∈ (computePrimaryGenerators K A e f j polynomials multiplicities).1 ℓ} := by
  rw [computePrimaryGenerators_eq_model]
  simp only [hr]
  exact primaryGeneratorsModel_correct K hops A e he f hf hm _ hp

/-- Each generated layer has its specified vector rank. -/
theorem computePrimaryGenerators_ranks (K : Subfield ℂ) [DecidableEq K]
    [Operations K] (hops : Operations.IsCorrect K) {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (f : K[X]) (j : Fin q)
    (polynomials : Vector K[X] m)
    (multiplicities : Vector (Vector ℕ q) m)
    (hf : Irreducible f) (hm : f.Monic)
    (hp : ∀ i : Fin m, polynomials[i] = minimalAnnihilatingPolynomial K A (e i))
    (hr : ∀ i : Fin m, multiplicities[i][j] = multiplicity f polynomials[i])
    (ℓ : ℕ) (v : Fin n → K)
    (hv : v ∈ (computePrimaryGenerators K A e f j polynomials multiplicities).1 ℓ) :
    vectorRank K A f v = ℓ := by
  rw [computePrimaryGenerators_eq_model] at hv
  simp only [hr] at hv
  exact primaryGeneratorsModel_ranks K hops A e f hf hm _ hp ℓ v hv

end SympyProofs.JordanKrylov
