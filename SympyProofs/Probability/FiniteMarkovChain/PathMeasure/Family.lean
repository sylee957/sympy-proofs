module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Characterization

/-!
# The family of laws of one generator

A generator does not choose where the chain starts. So one generator `Q` has a whole
family of laws on paths, one for each starting distribution `p`. It is the map
`p ↦ chainLaw Q p`. This file describes that family.

* The law from `p` is the mixture of the laws from the single states, by
  `chainLaw_eq_sum`: pick the starting state by `p`, then run the law of that state.
  So the family is built from one law for each state, `chainLaw Q (PMF.pure i)`.
  Textbooks write this law `P_i`.
* Different starting distributions give different laws, by `chainLaw_injective`.
* Every law on paths with the transition probabilities of `Q` is the law of the chain
  for exactly one starting distribution, by `existsUnique_pmf_eq_chainLaw`. So these
  laws and the starting distributions match one to one.
* Started in state `i`, the chain is in state `j` at time `t` with probability
  `transition Q t i j`, by `chainLaw_pure_coordinate`. This holds for every state `i`.

A single process only tests the states that it visits, so its transition probabilities
leave the rows of the other states of the generator free. The family tests every
state, because every state is the start of one of its members. So the family
determines the whole generator, which is `eq_of_chainLaw_pure_eq`. This is also why
textbooks can define the transition function through time `0`: they work with the
family, where every state can occur at time `0`.

The mixture holds for every matrix `Q`, because the finite laws are mixtures by
definition.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Mixture

variable (Q : Matrix ι ι ℝ) (d : ι)

/-- The finite laws from `p` are the mixture of the finite laws from each state. -/
private theorem finiteLaw_eq_bind (p : PMF ι) (I : Finset ℝ≥0) :
    finiteLaw Q d p I = p.bind fun i => finiteLaw Q d (PMF.pure i) I := by
  simp only [finiteLaw, sampledPath, PMF.map_bind, PMF.pure_bind]

variable [MeasurableSpace ι]

/-- The law of the chain from `p` is the mixture of the laws from each state. -/
theorem chainLaw_eq_sum (p : PMF ι) :
    chainLaw Q p = ∑ i, p i • chainLaw Q (PMF.pure i) := by
  refine (chainLaw_isProjectiveLimit Q p).unique fun I => ?_
  ext S hS
  change _ = (finiteLaw Q (filler p) p I).toMeasure S
  rw [Measure.map_apply (Finset.measurable_restrict I) hS, Measure.coe_finsetSum,
    Finset.sum_apply, finiteLaw_eq_bind, PMF.toMeasure_bind_apply _ _ _ hS, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul,
    ← Measure.map_apply (Finset.measurable_restrict I) hS,
    chainLaw_isProjectiveLimit Q (PMF.pure i) I, filler_eq (PMF.pure i) p]

end Mixture

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {Q : Matrix ι ι ℝ}

/-- Different starting distributions give different laws. -/
theorem chainLaw_injective (Q : Matrix ι ι ℝ) : Function.Injective (chainLaw Q) := by
  intro p p' h
  have h0 := congrArg (fun μ : Measure (Path ι) => μ.map (coordinate 0)) h
  simp only [chainLaw_initial] at h0
  exact PMF.toMeasure_injective h0

/-- Every law on paths with the transition probabilities of `Q` is the law of the chain
for exactly one starting distribution. -/
theorem existsUnique_pmf_eq_chainLaw (hQ : IsGenerator Q) (μ : Measure (Path ι))
    [IsProbabilityMeasure μ] (hm : IsHomogeneousMarkovProcess coordinate μ)
    (ht : HasTransition Q coordinate μ) : ∃! p : PMF ι, μ = chainLaw Q p := by
  have : IsProbabilityMeasure (μ.map (coordinate 0)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_coordinate 0).aemeasurable).2
      inferInstance
  refine ⟨(μ.map (coordinate 0)).toPMF, ?_, fun p hp => ?_⟩
  · exact (eq_chainLaw_iff hQ _ μ).2 ⟨(Measure.toPMF_toMeasure _).symm, hm, ht⟩
  · refine PMF.toMeasure_injective ?_
    rw [Measure.toPMF_toMeasure, hp, chainLaw_initial]

/-- Started in state `i`, the chain is in state `j` at time `t` with probability
`transition Q t i j`. This holds for every state `i`. -/
theorem chainLaw_pure_coordinate (hQ : IsGenerator Q) (i j : ι) (t : ℝ≥0) :
    chainLaw Q (PMF.pure i) {ω | ω t = j} = ENNReal.ofReal (transition Q t i j) := by
  have h := congrArg (fun μ : Measure ι => μ {j})
    (chainLaw_coordinate Q (PMF.pure i) t)
  simp only [PMF.pure_bind] at h
  rw [Measure.map_apply (measurable_coordinate t) (measurableSet_singleton j),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), step_apply hQ] at h
  exact h

/-- The laws from the single states determine the generator. No state has to be visited
by one particular process. -/
theorem eq_of_chainLaw_pure_eq {Q' : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (hQ' : IsGenerator Q')
    (h : ∀ i, chainLaw Q (PMF.pure i) = chainLaw Q' (PMF.pure i)) : Q = Q' := by
  refine transition_injective fun t => ?_
  ext i j
  have h1 := chainLaw_pure_coordinate hQ i j t
  rw [h i, chainLaw_pure_coordinate hQ' i j t] at h1
  exact ((ENNReal.ofReal_eq_ofReal_iff
    ((hQ'.transition_mem_rowStochastic t t.coe_nonneg).1 i j)
    ((hQ.transition_mem_rowStochastic t t.coe_nonneg).1 i j)).1 h1).symm

end SympyProofs.FiniteMarkovChain
