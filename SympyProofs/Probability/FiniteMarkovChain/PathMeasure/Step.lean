module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The transition law from one state

For a generator `Q` and a nonnegative time `t`, row `i` of `transition Q t` has
nonnegative entries that sum to one. It is the law of the state after that time, for
a chain in state `i` now. `step Q t i` is that law as a Mathlib `PMF`. The path
measure is constructed by sampling from these.

A `PMF` carries the proof that its masses sum to one, so `step` is defined by cases.
For a matrix that is not a generator the chain stays where it is, which keeps the
semigroup law `step_add` true for every matrix. The generator hypothesis is needed
only to read the masses as entries of `transition Q t`.

The reading for a process is `HasTransition` in `Process.Transition`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped ENNReal NNReal Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entries of a generator's transition matrix are nonnegative. -/
theorem IsGenerator.transition_nonneg {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) (t : ℝ≥0)
    (i j : ι) : 0 ≤ transition Q t i j :=
  (hQ.transition_mem_rowStochastic t t.coe_nonneg).1 i j

open scoped Classical in
/-- The transition law from one state, as a probability mass function. -/
noncomputable def step (Q : Matrix ι ι ℝ) (t : ℝ≥0) (i : ι) : PMF ι :=
  if h : IsGenerator Q then
    PMF.ofFintype (fun j => ENNReal.ofReal (transition Q t i j)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h.transition_nonneg t i j),
        Matrix.sum_row_of_mem_rowStochastic
          (h.transition_mem_rowStochastic t t.coe_nonneg) i]
      simp)
  else PMF.pure i

theorem step_apply {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) (t : ℝ≥0) (i j : ι) :
    step Q t i j = ENNReal.ofReal (transition Q t i j) := by
  simp only [step, hQ, ↓reduceDIte]
  rfl

@[simp] theorem step_zero (Q : Matrix ι ι ℝ) (i : ι) : step Q 0 i = PMF.pure i := by
  by_cases hQ : IsGenerator Q
  · ext j
    rw [step_apply hQ]
    by_cases h : i = j <;> simp [h, eq_comm]
  · simp [step, hQ]

theorem step_add (Q : Matrix ι ι ℝ) (s t : ℝ≥0) (i : ι) :
    (step Q s i).bind (step Q t) = step Q (s + t) i := by
  by_cases hQ : IsGenerator Q
  · ext j
    simp only [PMF.bind_apply, step_apply hQ, tsum_fintype, NNReal.coe_add,
      transition_add, Matrix.mul_apply]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg
      (hQ.transition_nonneg s i k) (hQ.transition_nonneg t k j))]
    exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_mul
      (hQ.transition_nonneg s i k)).symm
  · simp [step, hQ]

end SympyProofs.FiniteMarkovChain
