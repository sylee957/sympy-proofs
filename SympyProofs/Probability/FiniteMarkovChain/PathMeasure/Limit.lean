module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Characterization
public import SympyProofs.Probability.FiniteMarkovChain.Process.Bundled
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
* `w` is the limiting distribution of `Q` exactly when every process of `Q` has the
  limiting law `w`, by `isLimitingDistribution_iff_forall_isLimitingLaw`.

Each matrix notion is matched with the process notion of the same kind: stationary with
stationary, limiting with limiting. The first says "some process" and the second
"every process", because a stationary distribution fixes the start and a limiting
distribution does not depend on it.

The statements speak about a process on any probability space, as a `Process ι`, and
mention no measure on paths. The proofs need that processes exist, with every start.
That is why the file is in this folder: the process is the coordinate process under
`chainLaw Q p`.

The matrix notions and the links between them are in `LongRun`.
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
      ∃ S : Process ι, IsHomogeneousMarkovProcess S.X S.P ∧ HasTransition Q S.X S.P ∧
        IsStationaryLaw S.X S.P w := by
  constructor
  · intro hw
    -- start the chain from `w`
    have hsum : ∑ i, ENNReal.ofReal (w i) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw.nonneg i, hw.sum_eq_one,
        ENNReal.ofReal_one]
    have hp : (fun i => ((PMF.ofFintype (fun i => ENNReal.ofReal (w i)) hsum) i).toReal) = w :=
      funext fun i => by simp [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw.nonneg i)]
    refine ⟨⟨Path ι, chainLaw Q (PMF.ofFintype _ hsum), coordinate⟩,
      chainLaw_isHomogeneousMarkovProcess hQ _, chainLaw_hasTransition hQ _, fun t j => ?_⟩
    change (chainLaw Q (PMF.ofFintype _ hsum)).real {ω | coordinate t ω = j} = w j
    rw [chainLaw_real_coordinate hQ, hp, hw.balance.isInvariant t t.coe_nonneg]
  · rintro ⟨S, hm, ht, hw⟩
    exact hw.isStationaryDistribution hm.measurable hQ ht

/-- The limiting distribution of a generator is the limiting law of every one of its
processes, and a row that is the limiting law of every process is the limiting
distribution. -/
theorem isLimitingDistribution_iff_forall_isLimitingLaw (hQ : IsGenerator Q) (w : ι → ℝ) :
    IsLimitingDistribution Q w ↔
      ∀ S : Process ι, IsHomogeneousMarkovProcess S.X S.P → HasTransition Q S.X S.P →
        IsLimitingLaw S.X S.P w := by
  constructor
  · exact fun hw S hm ht => hw.isLimitingLaw hm.measurable hQ ht
  · intro h i j
    -- the process that starts in state `i`
    have hl : IsLimitingLaw coordinate (chainLaw Q (PMF.pure i)) w :=
      h ⟨Path ι, chainLaw Q (PMF.pure i), coordinate⟩
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

end SympyProofs.FiniteMarkovChain
