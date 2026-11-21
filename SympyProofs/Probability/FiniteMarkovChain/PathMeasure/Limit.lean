module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Characterization
public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# The processes of a generator in the long run

One generator `Q` has many processes, on many probability spaces and with many starts.
`LongRun` links the stationary and the limiting law of one given process to the
matrix. This file goes the other way: it reads the matrix notions as statements about
the processes of `Q`.

* `w` is a stationary distribution of `Q` exactly when some process of `Q` has the
  stationary law `w`, by `isStationaryDistribution_iff_exists_isStationaryLaw`. The
  process is the one that starts from `w`.
* `w` is a stationary distribution of `Q` exactly when some process of `Q` has the
  limiting law `w`, by `isStationaryDistribution_iff_exists_isLimitingLaw`. So the
  limiting laws that occur are exactly the stationary distributions.
* `w` is the limiting distribution of `Q` exactly when every process of `Q` has the
  limiting law `w`, by `isLimitingDistribution_iff_forall_isLimitingLaw`.
* All processes have the same limiting law exactly when some state can be reached from
  every state, by `exists_reachable_iff_exists_forall_isLimitingLaw`.

The statements speak about a process on any probability space and mention no measure on
paths. The proofs need that processes exist, with every start. That is why the file is
in this folder: the process is the coordinate process under `chainLaw Q p`.

The matrix statements behind the last three are in `LongRun.MatrixLimiting`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Matrix Filter Topology
open scoped NNReal ENNReal

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {Q : Matrix ι ι ℝ}

/-- A stationary distribution of a generator is the stationary law of some process, and
every stationary law of a process is a stationary distribution. -/
theorem isStationaryDistribution_iff_exists_isStationaryLaw (hQ : IsGenerator Q)
    (w : ι → ℝ) :
    IsStationaryDistribution Q w ↔
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℝ≥0 → Ω → ι),
        IsProbabilityMeasure P ∧ IsHomogeneousMarkovProcess X P ∧ HasTransition Q X P ∧
          IsStationaryLaw X P w := by
  constructor
  · intro hw
    -- start the chain from `w`
    have hsum : ∑ i, ENNReal.ofReal (w i) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw.nonneg i, hw.sum_eq_one,
        ENNReal.ofReal_one]
    have hp : (fun i => ((PMF.ofFintype (fun i => ENNReal.ofReal (w i)) hsum) i).toReal) = w :=
      funext fun i => by simp [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw.nonneg i)]
    refine ⟨Path ι, inferInstance, chainLaw Q (PMF.ofFintype _ hsum), coordinate,
      inferInstance, chainLaw_isHomogeneousMarkovProcess hQ _, chainLaw_hasTransition hQ _,
      fun t j => ?_⟩
    rw [chainLaw_real_coordinate hQ, hp, hw.balance.isInvariant t t.coe_nonneg]
  · rintro ⟨Ω, _, P, X, _, hm, ht, hw⟩
    exact hw.isStationaryDistribution hm.measurable hQ ht

/-- The limiting laws of the processes of a generator are exactly its stationary
distributions. -/
theorem isStationaryDistribution_iff_exists_isLimitingLaw (hQ : IsGenerator Q)
    (w : ι → ℝ) :
    IsStationaryDistribution Q w ↔
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℝ≥0 → Ω → ι),
        IsProbabilityMeasure P ∧ IsHomogeneousMarkovProcess X P ∧ HasTransition Q X P ∧
          IsLimitingLaw X P w := by
  constructor
  · intro hw
    obtain ⟨Ω, _, P, X, hP, hm, ht, hs⟩ :=
      (isStationaryDistribution_iff_exists_isStationaryLaw hQ w).1 hw
    exact ⟨Ω, _, P, X, hP, hm, ht, hs.isLimitingLaw⟩
  · rintro ⟨Ω, _, P, X, _, hm, ht, hw⟩
    exact hw.isStationaryDistribution hm.measurable hQ ht

/-- The limiting distribution of a generator is the limiting law of every one of its
processes, and a row that is the limiting law of every process is the limiting
distribution. -/
theorem isLimitingDistribution_iff_forall_isLimitingLaw (hQ : IsGenerator Q) (w : ι → ℝ) :
    IsLimitingDistribution Q w ↔
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → ι),
          IsHomogeneousMarkovProcess X P → HasTransition Q X P → IsLimitingLaw X P w := by
  constructor
  · exact fun hw Ω _ P _ X hm ht => hw.isLimitingLaw hm.measurable hQ ht
  · intro h i j
    -- the process that starts in state `i`
    have hl := h (Path ι) (chainLaw Q (PMF.pure i)) coordinate
      (chainLaw_isHomogeneousMarkovProcess hQ _) (chainLaw_hasTransition hQ _)
    have hf := (isLimitingLaw_iff_isLimitFrom measurable_coordinate hQ
      (chainLaw_hasTransition hQ (PMF.pure i)) w).1 hl
    have hp : (fun k => (chainLaw Q (PMF.pure i)).real {ω | coordinate 0 ω = k}) =
        Pi.single i 1 := by
      funext k
      rw [chainLaw_real_initial]
      by_cases hk : k = i <;> simp [PMF.pure_apply, hk]
    rw [hp] at hf
    have h1 := tendsto_pi_nhds.1 hf j
    simp only [single_one_vecMul] at h1
    exact h1

/-- All processes of a generator have the same limiting law exactly when some state can
be reached from every state. -/
theorem exists_reachable_iff_exists_forall_isLimitingLaw [Nonempty ι]
    (hQ : IsGenerator Q) :
    (∃ j₀, ∀ i, Reachable Q i j₀) ↔
      ∃ w : ι → ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ι),
          IsHomogeneousMarkovProcess X P → HasTransition Q X P →
            IsLimitingLaw X P w := by
  rw [← exists_isLimitingDistribution_iff hQ]
  exact exists_congr fun w => isLimitingDistribution_iff_forall_isLimitingLaw hQ w

end SympyProofs.FiniteMarkovChain
