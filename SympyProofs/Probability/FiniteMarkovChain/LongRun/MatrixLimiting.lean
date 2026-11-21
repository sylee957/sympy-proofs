module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.LimitEquation

/-!
# The limiting distribution of a generator

This file is about matrices only. It states two notions.

`IsLimitFrom Q p w` says that `w` is the limit of the chain with generator `Q` started
from the row `p`: the row `p ᵥ* transition Q t` tends to `w` as time grows. This is the
definition, and it is not a way to compute `w`.

For a generator there is exactly one such `w` for every `p`, by
`existsUnique_isLimitFrom`. It is `p ᵥ* limitMatrix Q`, by
`isLimitFrom_iff_eq_vecMul_limitMatrix`. It solves the balance equation and has the
same total mass as `p`, by `IsLimitFrom.balance` and `IsLimitFrom.sum_eq`. The row `p`
need not be a distribution. Every statement holds for any real row.

`IsLimitingDistribution Q w` says that `w` is the limiting distribution of the chain:
from every state `i`, the probability of being in state `j` tends to `w j`. This is the
definition in textbooks. The limit must not depend on the start. It is the same as
`IsLimitFrom Q p w` for every row `p` of total mass one, by
`isLimitingDistribution_iff_forall_isLimitFrom`.

The two notions of this file and the stationary distribution are related like this.

* The limits from the starting distributions are exactly the stationary distributions
  of `Q`, by `isStationaryDistribution_iff_exists_isLimitFrom`. A limit is always
  stationary, and a stationary distribution is the limit from itself.
* The limit is the same from every starting distribution exactly when some state can be
  reached from every state, by `exists_reachable_iff_exists_forall_isLimitFrom`.
* So a limiting distribution is a stationary distribution, and a generator has one
  exactly when some state can be reached from every state. These are
  `isLimitingDistribution_iff` and `exists_isLimitingDistribution_iff`.

A generator always has a stationary distribution and a limit from every start. It has
a limiting distribution only under the condition, and then the three are the same row.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix Filter Topology
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} {p w : ι → ℝ}

/-! ### The limit from a starting row -/

/-- `w` is the limit of the chain with generator `Q` started from the row `p`: the row
`p ᵥ* transition Q t` tends to `w` as time grows. -/
def IsLimitFrom (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w)

/-- The limit from `p` is `p` times the limit matrix. -/
theorem isLimitFrom_iff_eq_vecMul_limitMatrix (hQ : IsGenerator Q) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ w = p ᵥ* limitMatrix Q :=
  ⟨fun h => tendsto_nhds_unique h (tendsto_vecMul_transition_limitMatrix hQ p),
    fun h => h ▸ tendsto_vecMul_transition_limitMatrix hQ p⟩

/-- For a generator, every starting row has exactly one limit. -/
theorem existsUnique_isLimitFrom (hQ : IsGenerator Q) (p : ι → ℝ) :
    ∃! w : ι → ℝ, IsLimitFrom Q p w :=
  ⟨p ᵥ* limitMatrix Q, tendsto_vecMul_transition_limitMatrix hQ p,
    fun w hw => (isLimitFrom_iff_eq_vecMul_limitMatrix hQ p w).1 hw⟩

/-- The limit solves the balance equation. -/
theorem IsLimitFrom.balance (hQ : IsGenerator Q) (h : IsLimitFrom Q p w) : Balance Q w := by
  rw [(isLimitFrom_iff_eq_vecMul_limitMatrix hQ p w).1 h]
  exact balance_vecMul_limitMatrix hQ p

/-- The limit has the same total mass as the start. -/
theorem IsLimitFrom.sum_eq (hQ : IsGenerator Q) (h : IsLimitFrom Q p w) :
    ∑ i, w i = ∑ i, p i := by
  rw [(isLimitFrom_iff_eq_vecMul_limitMatrix hQ p w).1 h, ← dotProduct_one,
    ← dotProduct_one, vecMul_limitMatrix_dotProduct hQ p hQ.mulVec_one_eq_zero]

/-! ### The limits from all starting distributions -/

/-- The limits from the starting distributions are exactly the stationary distributions
of the generator. -/
theorem isStationaryDistribution_iff_exists_isLimitFrom (hQ : IsGenerator Q) (w : ι → ℝ) :
    IsStationaryDistribution Q w ↔
      ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ IsLimitFrom Q p w := by
  constructor
  · intro hw
    exact ⟨w, hw.nonneg, hw.sum_eq_one, tendsto_const_nhds.congr fun t =>
      (vecMul_transition_of_vecMul_eq_zero hw.balance t).symm⟩
  · rintro ⟨p, hp0, hp1, hw⟩
    obtain ⟨v, hv, hpv⟩ := exists_isStationaryDistribution_tendsto hQ hp0 hp1
    rwa [tendsto_nhds_unique hw hpv]

/-- The limit is the same from every starting distribution exactly when some state can
be reached from every state. -/
theorem exists_reachable_iff_exists_forall_isLimitFrom [Nonempty ι] (hQ : IsGenerator Q) :
    (∃ j₀, ∀ i, Reachable Q i j₀) ↔
      ∃ w : ι → ℝ, ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → IsLimitFrom Q p w := by
  constructor
  · rintro ⟨j₀, h⟩
    obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ h
    exact ⟨w, fun p _ hp1 => hw.tendsto_vecMul_transition hQ h hp1⟩
  · rintro ⟨w, hw⟩
    -- a stationary distribution is the limit from itself, so it is `w`
    refine exists_reachable_of_isStationaryDistribution_unique hQ fun v v' hv hv' => ?_
    have hself : ∀ u, IsStationaryDistribution Q u → u = w := fun u hu =>
      tendsto_nhds_unique (tendsto_const_nhds.congr fun t =>
        (vecMul_transition_of_vecMul_eq_zero hu.balance t).symm)
        (hw u hu.nonneg hu.sum_eq_one)
    exact (hself v hv).trans (hself v' hv').symm

/-! ### The limiting distribution -/

/-- `w` is the limiting distribution of the chain with generator `Q`: from every state
`i`, the probability of being in state `j` tends to `w j` as time grows. -/
def IsLimitingDistribution (Q : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  ∀ i j, Tendsto (fun t : ℝ => transition Q t i j) atTop (𝓝 (w j))

/-- The limiting distribution is the limit from every start of total mass one. -/
theorem isLimitingDistribution_iff_forall_isLimitFrom (Q : Matrix ι ι ℝ) (w : ι → ℝ) :
    IsLimitingDistribution Q w ↔ ∀ p : ι → ℝ, ∑ i, p i = 1 → IsLimitFrom Q p w := by
  constructor
  · intro h p hp
    refine tendsto_pi_nhds.2 fun j => ?_
    have h1 := tendsto_finsetSum Finset.univ fun i _ => (h i j).const_mul (p i)
    rw [← Finset.sum_mul, hp, one_mul] at h1
    exact h1
  · intro h i j
    have h1 := tendsto_pi_nhds.1 (h (Pi.single i 1) (by simp)) j
    simp only [single_one_vecMul] at h1
    exact h1

/-- A limiting distribution is a stationary distribution, and a stationary distribution
is the limiting distribution when some state can be reached from every state. -/
theorem isLimitingDistribution_iff [Nonempty ι] (hQ : IsGenerator Q) (w : ι → ℝ) :
    IsLimitingDistribution Q w ↔
      IsStationaryDistribution Q w ∧ ∃ j₀, ∀ i, Reachable Q i j₀ := by
  rw [isLimitingDistribution_iff_forall_isLimitFrom]
  constructor
  · intro h
    have i : ι := Classical.arbitrary ι
    refine ⟨(isStationaryDistribution_iff_exists_isLimitFrom hQ w).2
        ⟨Pi.single i 1, fun j => ?_, by simp, h _ (by simp)⟩,
      (exists_reachable_iff_exists_forall_isLimitFrom hQ).2 ⟨w, fun p _ hp => h p hp⟩⟩
    by_cases hj : j = i <;> simp [hj]
  · rintro ⟨hw, j₀, h⟩ p hp
    exact hw.tendsto_vecMul_transition hQ h hp

/-- A generator has a limiting distribution exactly when some state can be reached from
every state. -/
theorem exists_isLimitingDistribution_iff [Nonempty ι] (hQ : IsGenerator Q) :
    (∃ w, IsLimitingDistribution Q w) ↔ ∃ j₀, ∀ i, Reachable Q i j₀ := by
  constructor
  · rintro ⟨w, hw⟩
    exact ((isLimitingDistribution_iff hQ w).1 hw).2
  · rintro ⟨j₀, h⟩
    obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ h
    exact ⟨w, (isLimitingDistribution_iff hQ w).2 ⟨hw, j₀, h⟩⟩

end SympyProofs.FiniteMarkovChain
