module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.MatrixStationary
public import SympyProofs.Probability.FiniteMarkovChain.Process.Transition

/-!
# The stationary law of a process

`IsStationaryLaw X P w` says that the state of the process has the law `w` at every
time. It is stated for the process alone, with no matrix.

Take a process whose transition probabilities are those of a generator `Q`. It has the
stationary law `w` exactly when it starts from `w` and `w` solves the balance equation
`w ᵥ* Q = 0`. This is `isStationaryLaw_iff`. `balance_iff_stationary_process` is the
same fact with probabilities as extended nonnegative reals.

So the balance equation is the condition for the chain to be stationary. The statements
are about any process on any probability space.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Matrix
open scoped NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- The state of the process has the law `w` at every time. -/
def IsStationaryLaw (X : ℝ≥0 → Ω → ι) (P : Measure Ω) (w : ι → ℝ) : Prop :=
  ∀ t j, P.real {ω | X t ω = j} = w j

/-- A process has the stationary law `w` exactly when it starts from `w` and `w` solves
the balance equation. -/
theorem isStationaryLaw_iff {X : ℝ≥0 → Ω → ι} {P : Measure Ω} [IsFiniteMeasure P]
    (hX : ∀ t, Measurable (X t)) {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (ht : HasTransition Q X P) (w : ι → ℝ) :
    IsStationaryLaw X P w ↔ (∀ i, P.real {ω | X 0 ω = i} = w i) ∧ Balance Q w := by
  constructor
  · intro h
    have h0 : (fun i => P.real {ω | X 0 ω = i}) = w := funext (h 0)
    refine ⟨h 0, IsInvariant.balance fun t ht0 => funext fun j => ?_⟩
    have h1 := ht.measureReal_time hX hQ ⟨t, ht0⟩ j
    rw [h0, h ⟨t, ht0⟩ j] at h1
    exact h1.symm
  · rintro ⟨h0, hb⟩ t j
    rw [ht.measureReal_time hX hQ t j, funext h0, hb.isInvariant t t.coe_nonneg]

/-- Stationarity read on a process: the balance equation holds exactly when the state
has the same law at every time. -/
theorem balance_iff_stationary_process {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
    (hX : ∀ t, Measurable (X t)) {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q)
    (ht : HasTransition Q X P) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h0 : ∀ i, P {ω | X 0 ω = i} = ENNReal.ofReal (w i)) :
    Balance Q w ↔ ∀ (t : ℝ≥0) (j : ι), P {ω | X t ω = j} = P {ω | X 0 ω = j} := by
  have key := ht.measure_time hX hQ hw h0
  rw [balance_iff_isInvariant]
  constructor
  · intro hinv t j
    rw [key t j, hinv t t.coe_nonneg, h0 j]
  · intro h t ht0
    funext j
    have e := h ⟨t, ht0⟩ j
    rw [key ⟨t, ht0⟩ j, h0 j] at e
    exact (ENNReal.ofReal_eq_ofReal_iff
      (Matrix.nonneg_vecMul_of_mem_rowStochastic (hQ.transition_mem_rowStochastic t ht0) hw j)
      (hw j)).1 e

end SympyProofs.FiniteMarkovChain
