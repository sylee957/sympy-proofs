import SympyProofs.JordanKrylov.Algorithms.PrimaryGeneratingLemmas

/-! # Correctness of primary generator computation

The output generates the primary kernel, and each layer has its prescribed rank.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1 is correct when its polynomial inputs are a spanning family's
minimal annihilating polynomials. -/
theorem computePrimaryGenerators_correct (K : Subfield ℂ) [DecidableEq K]
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (he : Submodule.span K (Set.range e) = ⊤) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i)) :
    IsKrylovGeneratingSet K A (powerKernel K A f (multiplicity f (minpoly K A)))
      {v | ∃ ℓ, v ∈ computePrimaryGenerators K A e f p ℓ} := by
  rw [computePrimaryGenerators_eq K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)]
  have hp' : p = fun i => minimalAnnihilatingPolynomial K A (e i) := funext hp
  subst p
  exact primaryGeneratingSet_isKrylovGeneratingSet_minpoly K A e he f hf hm _
    (fun i => primaryCofactor_factorization K f _ hf.ne_zero)

/-- Every returned vector has the rank indexing its list. -/
theorem computePrimaryGenerators_ranks (K : Subfield ℂ) [DecidableEq K]
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (e : Fin m → (Fin n → K))
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (p : Fin m → K[X]) (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (ℓ : ℕ) (v : Fin n → K) (hv : v ∈ computePrimaryGenerators K A e f p ℓ) :
    vectorRank K A f v = ℓ := by
  rw [mem_computePrimaryGenerators K hops A e f hf hm p
    (fun i => (hp i) ▸ (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero)] at hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  have hi := (Finset.mem_filter.mp hi).2.2
  rw [hp i] at hi ⊢
  exact (vectorRank_primaryCofactor K A f hf (e i)).trans hi

end SympyProofs.JordanKrylov
