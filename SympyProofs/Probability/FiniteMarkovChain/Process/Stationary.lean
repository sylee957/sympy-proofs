module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Stationary
public import SympyProofs.Probability.FiniteMarkovChain.Process.Transition

/-!
# Stationary processes

Take a process whose transition probabilities are those of a generator `Q`, started
from a nonnegative row `w`. The row solves the balance equation `w ᵥ* Q = 0` exactly
when the state has the same law at every time. This is
`balance_iff_stationary_process`.

So the balance equation is the condition for the chain to be stationary. The statement
is about any process on any probability space.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory Matrix
open scoped NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

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
