import SympyProofs.JordanKrylov.Algorithms.GeneralizedEigenspace
import SympyProofs.JordanKrylov.Algorithms.RefinedJordanKrylovBasisCorrectness
import SympyProofs.JordanKrylov.Algorithms.JordanChainsCorrectness

/-! # Correctness of Algorithm 6

The input family need only span the ambient space. Correctness holds with or
without preprocessing, assuming the supplied polynomial operations are correct.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

variable (K : Subfield ℂ) [DecidableEq K] [PolynomialOperations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (e : Fin s → (Fin n → K)) (p : Fin s → K[X])
    (m : ℕ) (preprocess : Bool)
    (he : Submodule.span K (Set.range e) = ⊤)
    (hf : Irreducible f) (hm : f.Monic)
    (hp : ∀ i, p i = minimalAnnihilatingPolynomial K A (e i))
    (hmult : m = multiplicity f A.charpoly)
    (hops : PolynomialOperations.IsCorrect K)

include he hf hm hp hops

omit [DecidableEq K] in
/-- The computed rank bound equals the exponent of `f` in the minimal polynomial. -/
theorem primaryRankBound_eq :
    Finset.univ.sup (fun i => PolynomialOperations.multiplicity f (p i)) =
      multiplicity f (minpoly K A) := by
  rw [multiplicity_minpoly_eq_max_spanning K A e he f hf hm]
  apply Finset.sup_congr rfl
  intro i _
  rw [hops.multiplicity_eq f (p i) hf.natDegree_pos hm
    (by rw [hp i]; exact (minimalAnnihilatingPolynomial_monic K A (e i)).ne_zero), hp i]

include hmult

/-- The executable assembly agrees with the composition at the mathematical rank bound. -/
theorem computeGeneralizedEigenspace_eq :
    computeGeneralizedEigenspace K A f e p m preprocess =
      computeJordanChains K A f
        (computeRefinedJordanKrylovBasis K A f (computePrimaryGenerators K A e f p)
          (multiplicity f (minpoly K A)) (multiplicity f A.charpoly) preprocess)
        (multiplicity f (minpoly K A)) := by
  simp only [computeGeneralizedEigenspace, Id.run, pure]
  rw [primaryRankBound_eq K A f e p he hf hm hp hops, hmult]

/-- Every output evaluates to a Jordan chain at every root of `f`. -/
theorem computeGeneralizedEigenspace_correct
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    ∀ c ∈ computeGeneralizedEigenspace K A f e p m preprocess,
      IsJordanChain (A.map K.subtype).mulVecLin α (evaluateJordanChain K c α) := by
  rw [computeGeneralizedEigenspace_eq K A f e p m preprocess he hf hm hp hmult hops]
  apply computeJordanChains_correct K A f _ _ hops hf _ _ α hα
  · exact computeRefinedJordanKrylovBasis_correct K A e he f hf hm p hp preprocess hops
  · exact computeRefinedJordanKrylovBasis_ranks K A e he f hf hm p hp preprocess hops

/-- Distinct output chains have independent spans at each root. -/
theorem computeGeneralizedEigenspace_independent (α : ℂ) :
    iSupIndep (fun c : ↥(computeGeneralizedEigenspace K A f e p m preprocess) =>
      evaluatedChainSpace K c.val α) := by
  rw [computeGeneralizedEigenspace_eq K A f e p m preprocess he hf hm hp hmult hops]
  apply computeJordanChains_independent K A f _ _ hops
  · exact computeRefinedJordanKrylovBasis_correct K A e he f hf hm p hp preprocess hops
  · exact computeRefinedJordanKrylovBasis_ranks K A e he f hf hm p hp preprocess hops

/-- Evaluating at all roots spans the full complexified primary kernel. -/
theorem computeGeneralizedEigenspace_span
    (α : Fin f.natDegree → ℂ) (hinj : Function.Injective α)
    (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    (⨆ i, ⨆ c ∈ computeGeneralizedEigenspace K A f e p m preprocess,
      evaluatedChainSpace K c (α i)) =
      complexSpan K (powerKernel K A f (multiplicity f (minpoly K A))) := by
  rw [computeGeneralizedEigenspace_eq K A f e p m preprocess he hf hm hp hmult hops]
  apply computeJordanChains_span K A f _ _ hops hf hm _ _ α hinj hroot
  · exact computeRefinedJordanKrylovBasis_correct K A e he f hf hm p hp preprocess hops
  · exact computeRefinedJordanKrylovBasis_ranks K A e he f hf hm p hp preprocess hops

end SympyProofs.JordanKrylov
