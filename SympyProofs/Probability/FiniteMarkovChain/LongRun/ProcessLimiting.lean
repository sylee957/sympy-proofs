module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.MatrixLimiting
public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessStationary
public import SympyProofs.Probability.FiniteMarkovChain.Process.Generator

/-!
# The limiting law of a process

The limiting law of a process is where the law of its state goes as time
grows. `IsLimitingLaw X P w` states it for the process alone, with no matrix:
the probability that `X t` is `j` tends to `w j` for every state `j`.

Take a process with the transition probabilities of a generator `Q`.

* A limiting law is a stationary distribution of `Q`, by
  `IsLimitingLaw.isStationaryDistribution`. A limit is unchanged by waiting
  longer, and by `HasTransition.measureReal_time` waiting multiplies the law by a
  transition matrix.
* If some state can be reached from every state, a stationary distribution of `Q` is
  the limiting law, by
  `IsStationaryDistribution.isLimitingLaw`. This is the matrix statement in
  `Convergence` read on the process.

Under that condition the two notions agree, which is
`isLimitingLaw_iff_isStationaryDistribution`.

`exists_isLimitingLaw` starts from a time-homogeneous Markov process and
nothing else: it has a limiting law. No condition on which states can be
reached is needed for this. Without such a condition the limiting law depends
on the law of the process at time `0`, and the generator may have other stationary
distributions.

Without the condition the limiting law is the law at time `0` times the limit
matrix of `LimitMatrix`, by `HasTransition.isLimitingLaw`. It is also
determined by linear equations: it solves the balance equation, and it gives every column `h` with
`Q *ᵥ h = 0` the same value as the law at time `0` does. This is
`isLimitingLaw_iff_forall_dotProduct`, the matrix statement in
`LimitEquation` read on the process.

One process never has two limiting laws, because a limit is unique. This is
`IsLimitingLaw.eq`, and it needs no assumption on the process. So a
time-homogeneous Markov process has exactly one limiting law, which is
`existsUnique_isLimitingLaw`.

The limiting law is linked to the other three notions of this folder.

* It is the limit from the law at time `0`, in the sense of `IsLimitFrom`, by
  `isLimitingLaw_iff_isLimitFrom`.
* If the generator has a limiting distribution, that is the limiting law of every
  process, by `IsLimitingDistribution.isLimitingLaw`.
* A stationary law of the process is its limiting law, by
  `IsStationaryLaw.isLimitingLaw`, and so it is a stationary distribution of the
  generator, by `IsStationaryLaw.isStationaryDistribution`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Matrix Filter Topology
open scoped NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}

/-- The law of the state of the process converges to `w` as time grows. -/
def IsLimitingLaw (X : ℝ≥0 → Ω → ι) (P : Measure Ω) (w : ι → ℝ) : Prop :=
  ∀ j, Tendsto (fun t : ℝ≥0 => P.real {ω | X t ω = j}) atTop (𝓝 (w j))

/-- A process has at most one limiting law. -/
theorem IsLimitingLaw.eq {w w' : ι → ℝ} (hw : IsLimitingLaw X P w)
    (hw' : IsLimitingLaw X P w') : w = w' :=
  funext fun j => tendsto_nhds_unique (hw j) (hw' j)

/-- A law that the process has at every time is its limiting law. -/
theorem IsStationaryLaw.isLimitingLaw {w : ι → ℝ} (h : IsStationaryLaw X P w) :
    IsLimitingLaw X P w :=
  fun j => tendsto_const_nhds.congr fun t => (h t j).symm

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [IsProbabilityMeasure P]

/-- The probabilities of the states at one time sum to one. -/
private theorem sum_measureReal_time (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    ∑ j, P.real {ω | X t ω = j} = 1 := by
  have hs := sum_measure_preimage_singleton (μ := P) Finset.univ (f := X t)
    (fun i _ => hX t (measurableSet_singleton i))
  rw [Finset.coe_univ, Set.preimage_univ, measure_univ] at hs
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum fun i _ => measure_ne_top P _]
  exact (congrArg ENNReal.toReal hs).trans ENNReal.toReal_one

variable [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- A limiting law is a stationary distribution of the generator. -/
theorem IsLimitingLaw.isStationaryDistribution (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) {w : ι → ℝ}
    (hw : IsLimitingLaw X P w) : IsStationaryDistribution Q w := by
  refine ⟨fun j => ge_of_tendsto' (hw j) fun t => ENNReal.toReal_nonneg, ?_, ?_⟩
  · have h1 : Tendsto (fun t : ℝ≥0 => ∑ j, P.real {ω | X t ω = j}) atTop
        (𝓝 (∑ j, w j)) := tendsto_finsetSum _ fun j _ => hw j
    simp_rw [sum_measureReal_time hX] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- the rows `p ᵥ* transition Q t` converge to `w`
  let p : ι → ℝ := fun i => P.real {ω | X 0 ω = i}
  have hrow : Tendsto (fun t : ℝ≥0 => p ᵥ* transition Q t) atTop (𝓝 w) :=
    tendsto_pi_nhds.2 fun j => (hw j).congr fun t => ht.measureReal_time hX hQ t j
  -- a limit is unchanged by waiting, so it is invariant
  refine IsInvariant.balance fun s hs => ?_
  have h1 : Tendsto (fun t : ℝ≥0 => (p ᵥ* transition Q t) ᵥ* transition Q s) atTop
      (𝓝 (w ᵥ* transition Q s)) :=
    ((continuous_id.matrix_vecMul continuous_const).tendsto w).comp hrow
  have h2 : Tendsto (fun t : ℝ≥0 => (p ᵥ* transition Q t) ᵥ* transition Q s) atTop
      (𝓝 w) := by
    have e : ∀ t : ℝ≥0, (p ᵥ* transition Q t) ᵥ* transition Q s =
        p ᵥ* transition Q ((t + ⟨s, hs⟩ : ℝ≥0) : ℝ) := fun t => by
      rw [← vecMul_transition_add]
      rfl
    simp_rw [e]
    exact hrow.comp (tendsto_atTop_mono (fun t : ℝ≥0 => le_self_add) tendsto_id)
  exact tendsto_nhds_unique h1 h2

/-- If some state can be reached from every state, a stationary distribution of the
generator is the limiting law of the process. -/
theorem IsStationaryDistribution.isLimitingLaw (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) {w : ι → ℝ} (hw : IsStationaryDistribution Q w) :
    IsLimitingLaw X P w := by
  intro j
  have hrow := (tendsto_pi_nhds.1 (hw.tendsto_vecMul_transition hQ h
    (p := fun i => P.real {ω | X 0 ω = i}) (sum_measureReal_time hX 0)) j).comp
    (NNReal.tendsto_coe_atTop.2 tendsto_id)
  exact hrow.congr fun t => (ht.measureReal_time hX hQ t j).symm

/-- If some state can be reached from every state, the limiting law of the
process and the stationary distribution of its generator are the same thing. -/
theorem isLimitingLaw_iff_isStationaryDistribution (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ IsStationaryDistribution Q w :=
  ⟨fun hw => hw.isStationaryDistribution hX hQ ht,
    fun hw => hw.isLimitingLaw hX hQ ht h⟩

/-- A time-homogeneous Markov process has a limiting law. No condition on which
states can be reached is needed. -/
theorem exists_isLimitingLaw (h : IsHomogeneousMarkovProcess X P) :
    ∃ w : ι → ℝ, IsLimitingLaw X P w := by
  obtain ⟨Q, hQ, hT⟩ := exists_generator_of_isHomogeneousMarkovProcess h
  obtain ⟨w, -, hw⟩ := exists_isStationaryDistribution_tendsto hQ
    (p := fun i => P.real {ω | X 0 ω = i}) (fun i => ENNReal.toReal_nonneg)
    (sum_measureReal_time h.measurable 0)
  refine ⟨w, fun j => ?_⟩
  have hrow := (tendsto_pi_nhds.1 hw j).comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  exact hrow.congr fun t => (hT.measureReal_time h.measurable hQ t j).symm

/-- The limiting law of a process is its law at time `0` times the limit
matrix. No condition on which states can be reached is needed. -/
theorem HasTransition.isLimitingLaw (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) :
    IsLimitingLaw X P ((fun i => P.real {ω | X 0 ω = i}) ᵥ* limitMatrix Q) :=
  fun j => ((tendsto_pi_nhds.1 (tendsto_vecMul_transition_limitMatrix hQ _) j).comp
    (NNReal.tendsto_coe_atTop.2 tendsto_id)).congr
      fun t => (ht.measureReal_time hX hQ t j).symm

/-- The limiting law of a process is the one solution `w` of the balance
equation that gives every column `h` with `Q *ᵥ h = 0` the same value as the law at time
`0` does. No condition on which states can be reached is needed. -/
theorem isLimitingLaw_iff_forall_dotProduct (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) (w : ι → ℝ) :
    IsLimitingLaw X P w ↔
      Balance Q w ∧ ∀ h : ι → ℝ, Q *ᵥ h = 0 →
        w ⬝ᵥ h = (fun i => P.real {ω | X 0 ω = i}) ⬝ᵥ h := by
  rw [← tendsto_vecMul_transition_iff_forall_dotProduct hQ]
  have hof : ∀ v : ι → ℝ,
      Tendsto (fun t : ℝ => (fun i => P.real {ω | X 0 ω = i}) ᵥ* transition Q t) atTop
        (𝓝 v) → IsLimitingLaw X P v := fun v hv j =>
    ((tendsto_pi_nhds.1 hv j).comp (NNReal.tendsto_coe_atTop.2 tendsto_id)).congr
      fun t => (ht.measureReal_time hX hQ t j).symm
  refine ⟨fun hw => ?_, hof w⟩
  obtain ⟨v, -, hv⟩ := exists_isStationaryDistribution_tendsto hQ
    (p := fun i => P.real {ω | X 0 ω = i}) (fun i => ENNReal.toReal_nonneg)
    (sum_measureReal_time hX 0)
  rwa [hw.eq (hof v hv)]

/-- A time-homogeneous Markov process has exactly one limiting law. -/
theorem existsUnique_isLimitingLaw (h : IsHomogeneousMarkovProcess X P) :
    ∃! w : ι → ℝ, IsLimitingLaw X P w := by
  obtain ⟨w, hw⟩ := exists_isLimitingLaw h
  exact ⟨w, hw, fun v hv => hv.eq hw⟩

/-! ### The links to the matrix notions -/

/-- The limiting law of a process is the limit from its law at time `0`. -/
theorem isLimitingLaw_iff_isLimitFrom
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ IsLimitFrom Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_forall_dotProduct hX hQ ht w).trans
    (tendsto_vecMul_transition_iff_forall_dotProduct hQ _ w).symm

/-- If the generator has a limiting distribution, it is the limiting law of every
process with its transition probabilities. -/
theorem IsLimitingDistribution.isLimitingLaw (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) {w : ι → ℝ}
    (hw : IsLimitingDistribution Q w) : IsLimitingLaw X P w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).2
    ((isLimitingDistribution_iff_forall_isLimitFrom Q w).1 hw _ (sum_measureReal_time hX 0))

/-- A stationary law of a process is a stationary distribution of the generator. -/
theorem IsStationaryLaw.isStationaryDistribution (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) {w : ι → ℝ}
    (hw : IsStationaryLaw X P w) : IsStationaryDistribution Q w :=
  hw.isLimitingLaw.isStationaryDistribution hX hQ ht

end SympyProofs.FiniteMarkovChain
