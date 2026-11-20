module

public import SympyProofs.Probability.FiniteMarkovChain.Process.Basic
public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Reachable

/-!
# Transition probabilities given by a matrix

`HasTransition Q X P` connects a process to a matrix: the chance of moving from `i` to
`j` over a duration `t` is `transition Q t i j`.

The transition probabilities determine the row of the generator at every state that
the process visits, by `HasTransition.generator_row_unique`. A state that is never
visited leaves its row free. If every state is visited at some time, the whole
generator is determined, by `HasTransition.generator_unique`.

`HasTransition.measure_time` gives the law of the state at any time: the starting row
times the transition matrix. `HasTransition.measureReal_time` is the same with real
probabilities and the law at time `0` as the starting row.

A process whose transition probabilities come from a matrix is time homogeneous and
does not leave its state instantly, by `HasTransition.homogeneousProduct` and
`HasTransition.continuousProduct`. So with the Markov property it is a time-homogeneous
Markov process, which is `HasTransition.isHomogeneousMarkovProcess`.

`Generator` proves that a generator exists for every time-homogeneous Markov process,
and `PathMeasure.Existence` proves that every generator has such a process.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Matrix

variable {ι Ω : Type*} [MeasurableSpace Ω]

variable [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} {X : ℝ≥0 → Ω → ι}
  {P : Measure Ω}

/-- The transition probabilities of the process `X` are the transition matrices of
`Q`: from state `i` at time `s`, the process is in `j` after a duration `t` with
probability `transition Q t i j`. -/
def HasTransition (Q : Matrix ι ι ℝ) (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop :=
  ∀ (s t : ℝ≥0) (i j : ι),
    P {ω | X s ω = i ∧ X (s + t) ω = j} =
      P {ω | X s ω = i} * ENNReal.ofReal (transition Q t i j)

/-- If the process moves from `i` to `j` with positive probability, then `j` can be
reached from `i`. -/
theorem HasTransition.reachable (ht : HasTransition Q X P) {s t : ℝ≥0} {i j : ι}
    (h : P {ω | X s ω = i ∧ X (s + t) ω = j} ≠ 0) : Reachable Q i j := by
  rw [ht s t i j] at h
  exact ⟨t, ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 (right_ne_zero_of_mul h))⟩

/-- The transition probabilities of a process determine the row of the generator at
every state that the process visits. -/
theorem HasTransition.generator_row_unique {Q' : Matrix ι ι ℝ} [IsFiniteMeasure P]
    (hQ : IsGenerator Q) (hQ' : IsGenerator Q')
    (h : HasTransition Q X P) (h' : HasTransition Q' X P)
    {i : ι} {s : ℝ≥0} (hs : P {ω | X s ω = i} ≠ 0) (j : ι) : Q i j = Q' i j := by
  refine transition_row_injective (fun t j => ?_) j
  have h1 := h s t i j
  rw [h' s t i j] at h1
  have h3 := (ENNReal.mul_right_inj hs (measure_ne_top P _)).1 h1
  exact ((ENNReal.ofReal_eq_ofReal_iff
    ((hQ'.transition_mem_rowStochastic t t.coe_nonneg).1 i j)
    ((hQ.transition_mem_rowStochastic t t.coe_nonneg).1 i j)).1 h3).symm

/-- If every state is visited at some time, the transition probabilities of a process
determine the generator. -/
theorem HasTransition.generator_unique {Q' : Matrix ι ι ℝ} [IsFiniteMeasure P]
    (hQ : IsGenerator Q) (hQ' : IsGenerator Q')
    (hvis : ∀ i, ∃ s : ℝ≥0, P {ω | X s ω = i} ≠ 0)
    (h : HasTransition Q X P) (h' : HasTransition Q' X P) : Q = Q' := by
  ext i j
  obtain ⟨s, hs⟩ := hvis i
  exact h.generator_row_unique hQ hQ' h' hs j

/-- A process whose transition probabilities come from a matrix is time homogeneous. -/
theorem HasTransition.homogeneousProduct (ht : HasTransition Q X P) :
    HomogeneousProduct X P := by
  intro s s' d i j
  rw [ht s d i j, ht s' d i j]
  ring

/-- A process whose transition probabilities come from a matrix does not leave its state
instantly. -/
theorem HasTransition.continuousProduct (ht : HasTransition Q X P) :
    ContinuousProduct X P := by
  intro s i
  simp_rw [ht s _ i i]
  have hc : Tendsto (fun t : ℝ≥0 => ENNReal.ofReal (transition Q (t : ℝ) i i)) (𝓝 0)
      (𝓝 (ENNReal.ofReal (transition Q ((0 : ℝ≥0) : ℝ) i i))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((hasDerivAt_transition_apply_zero Q i i).continuousAt.tendsto).comp
        (NNReal.continuous_coe.tendsto 0))
  have hm := ENNReal.Tendsto.const_mul (a := P {ω | X s ω = i}) hc (Or.inl (by simp))
  simpa using hm

variable [MeasurableSpace ι]

/-- A measurable process with the Markov property whose transition probabilities come
from a matrix is a time-homogeneous Markov process. Homogeneity and continuity are
automatic. -/
theorem HasTransition.isHomogeneousMarkovProcess (hX : ∀ t, Measurable (X t))
    (ht : HasTransition Q X P) (hm : MarkovPropertyProduct X P) :
    IsHomogeneousMarkovProcess X P :=
  ⟨hX, hm, ht.homogeneousProduct, ht.continuousProduct⟩

variable [MeasurableSingletonClass ι]

/-- The law of the state at time `t` is the starting row times the transition matrix. -/
theorem HasTransition.measure_time (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q)
    (ht : HasTransition Q X P) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (h0 : ∀ i, P {ω | X 0 ω = i} = ENNReal.ofReal (p i)) (t : ℝ≥0) (j : ι) :
    P {ω | X t ω = j} = ENNReal.ofReal ((p ᵥ* transition Q t) j) := by
  have hm : ∀ i, MeasurableSet {ω | X 0 ω = i} := fun i => hX 0 (measurableSet_singleton i)
  have hsum := sum_measure_preimage_singleton (μ := P.restrict {ω | X t ω = j})
    Finset.univ (f := X 0) (fun i _ => hm i)
  rw [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hsum
  rw [← hsum]
  simp only [Matrix.vecMul, dotProduct]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hp i)
    ((hQ.transition_mem_rowStochastic t t.coe_nonneg).1 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (hp i), ← h0 i]
  have e := ht 0 t i j
  rw [zero_add] at e
  exact (Measure.restrict_apply (hm i)).trans e

/-- The law of the state at time `t`, in real numbers, is the law at time `0` times the
transition matrix. -/
theorem HasTransition.measureReal_time [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t))
    (hQ : IsGenerator Q) (ht : HasTransition Q X P) (t : ℝ≥0) (j : ι) :
    P.real {ω | X t ω = j} = ((fun i => P.real {ω | X 0 ω = i}) ᵥ* transition Q t) j := by
  have hp : ∀ i, 0 ≤ P.real {ω | X 0 ω = i} := fun i => ENNReal.toReal_nonneg
  rw [measureReal_def, ht.measure_time hX hQ hp
    (fun i => (ENNReal.ofReal_toReal (measure_ne_top P _)).symm) t j,
    ENNReal.toReal_ofReal (Matrix.nonneg_vecMul_of_mem_rowStochastic
      (hQ.transition_mem_rowStochastic t t.coe_nonneg) hp j)]

end SympyProofs.FiniteMarkovChain
