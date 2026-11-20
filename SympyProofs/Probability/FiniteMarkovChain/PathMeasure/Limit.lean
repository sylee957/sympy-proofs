module

public import SympyProofs.Probability.FiniteMarkovChain.PathMeasure.Characterization
public import SympyProofs.Probability.FiniteMarkovChain.Process.Limit

/-!
# The limiting distributions of the family

One generator `Q` has a family of laws, `chainLaw hQ p`, one for each starting
distribution `p`. `Process.Limit` shows that each member has exactly one limiting
distribution. This file says what these limits are, for the family as a whole.

* The limit of the member that starts from `p` is the row `p` times the limit matrix,
  by `isLimitingDistribution_chainLaw_vecMul_limitMatrix`.
* That limit is determined by linear equations: it solves the balance equation, and it
  gives every column `h` with `Q *ᵥ h = 0` the same value as `p` does. This is
  `isLimitingDistribution_chainLaw_iff`.
* The limits that occur are exactly the stationary distributions of `Q`, by
  `isStationaryDistribution_iff_exists_isLimitingDistribution`. A limiting distribution
  is always stationary. Conversely, a chain that starts from a stationary distribution
  has that law at every time, so it is its own limit.
* All members have the same limit exactly when some state can be reached from every
  state, by `exists_reachable_iff_exists_forall_isLimitingDistribution`.

So the solutions of `w ᵥ* Q = 0` with nonnegative entries that sum to one are exactly
the limits that the chain can have, over all possible starts. There is one solution
exactly when the limit does not depend on the start.

Two facts about a single member are used. Under `chainLaw hQ p` the state at time `0`
has the law `p`, which is `chainLaw_real_initial`, and the state at time `t` has the
law `p` times `transition Q t`, which is `chainLaw_real_coordinate`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Matrix Filter Topology
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {Q : Matrix ι ι ℝ}

/-! ### The law of one member at each time -/

/-- Under the law of the chain from `p`, the state at time `0` is `i` with probability
`p i`. -/
theorem chainLaw_real_initial (hQ : IsGenerator Q) (p : PMF ι) (i : ι) :
    (chainLaw hQ p).real {ω | coordinate 0 ω = i} = (p i).toReal := by
  have h : (chainLaw hQ p).map (coordinate 0) {i} = p.toMeasure {i} := by
    rw [chainLaw_initial]
  rw [Measure.map_apply (measurable_coordinate 0) (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)] at h
  rw [measureReal_def]
  exact congrArg ENNReal.toReal h

/-- Under the law of the chain from `p`, the law of the state at time `t` is the row `p`
times the transition matrix. -/
theorem chainLaw_real_coordinate (hQ : IsGenerator Q) (p : PMF ι) (t : ℝ≥0) (j : ι) :
    (chainLaw hQ p).real {ω | coordinate t ω = j} =
      ((fun i => (p i).toReal) ᵥ* transition Q t) j := by
  have h := (chainLaw_hasTransition hQ p).measureReal_time measurable_coordinate hQ t j
  rw [show (fun i => (p i).toReal) =
    fun i => (chainLaw hQ p).real {ω | coordinate 0 ω = i} from
      funext fun i => (chainLaw_real_initial hQ p i).symm]
  exact h

/-! ### The limits of the family -/

/-- The limiting distribution of the member that starts from `p` is the row `p` times
the limit matrix. -/
theorem isLimitingDistribution_chainLaw_vecMul_limitMatrix (hQ : IsGenerator Q)
    (p : PMF ι) :
    IsLimitingDistribution coordinate (chainLaw hQ p)
      ((fun i => (p i).toReal) ᵥ* limitMatrix Q) := by
  have h := (chainLaw_hasTransition hQ p).isLimitingDistribution measurable_coordinate hQ
  simp_rw [chainLaw_real_initial hQ p] at h
  exact h

/-- The limiting distribution of the member that starts from `p` is the one solution `w`
of the balance equation that gives every column `h` with `Q *ᵥ h = 0` the same value as
`p` does. -/
theorem isLimitingDistribution_chainLaw_iff (hQ : IsGenerator Q) (p : PMF ι) (w : ι → ℝ) :
    IsLimitingDistribution coordinate (chainLaw hQ p) w ↔
      Balance Q w ∧ ∀ h : ι → ℝ, Q *ᵥ h = 0 →
        w ⬝ᵥ h = (fun i => (p i).toReal) ⬝ᵥ h := by
  rw [isLimitingDistribution_iff_forall_dotProduct measurable_coordinate hQ
    (chainLaw_hasTransition hQ p)]
  simp_rw [chainLaw_real_initial hQ p]

/-- The limiting distributions of the family are exactly the stationary distributions of
the generator. -/
theorem isStationaryDistribution_iff_exists_isLimitingDistribution (hQ : IsGenerator Q)
    (w : ι → ℝ) :
    IsStationaryDistribution Q w ↔
      ∃ p : PMF ι, IsLimitingDistribution coordinate (chainLaw hQ p) w := by
  constructor
  · intro hw
    have hsum : ∑ i, ENNReal.ofReal (w i) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw.nonneg i, hw.sum_eq_one,
        ENNReal.ofReal_one]
    refine ⟨PMF.ofFintype (fun i => ENNReal.ofReal (w i)) hsum, fun j => ?_⟩
    have hp : (fun i => ((PMF.ofFintype (fun i => ENNReal.ofReal (w i)) hsum) i).toReal) = w :=
      funext fun i => by simp [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw.nonneg i)]
    refine tendsto_const_nhds.congr fun t => ?_
    rw [chainLaw_real_coordinate hQ, hp, hw.balance.isInvariant t t.coe_nonneg]
  · rintro ⟨p, hp⟩
    exact hp.isStationaryDistribution measurable_coordinate hQ (chainLaw_hasTransition hQ p)

/-- All members of the family have the same limiting distribution exactly when some
state can be reached from every state. -/
theorem exists_reachable_iff_exists_forall_isLimitingDistribution [Nonempty ι]
    (hQ : IsGenerator Q) :
    (∃ j₀, ∀ i, Reachable Q i j₀) ↔
      ∃ w : ι → ℝ, ∀ p : PMF ι, IsLimitingDistribution coordinate (chainLaw hQ p) w := by
  constructor
  · rintro ⟨j₀, h⟩
    obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ h
    exact ⟨w, fun p => hw.isLimitingDistribution measurable_coordinate hQ
      (chainLaw_hasTransition hQ p) h⟩
  · rintro ⟨w, hw⟩
    refine exists_reachable_of_isStationaryDistribution_unique hQ fun v v' hv hv' => ?_
    obtain ⟨p, hp⟩ := (isStationaryDistribution_iff_exists_isLimitingDistribution hQ v).1 hv
    obtain ⟨p', hp'⟩ :=
      (isStationaryDistribution_iff_exists_isLimitingDistribution hQ v').1 hv'
    exact (hp.eq (hw p)).trans (hp'.eq (hw p')).symm

end SympyProofs.FiniteMarkovChain
