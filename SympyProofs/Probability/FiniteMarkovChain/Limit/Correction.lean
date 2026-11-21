module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# Method: a correction of the start

Solve `y ᵥ* (Q * Q) = -(p ᵥ* Q)` for a row `y`, and take `w = p + y ᵥ* Q`. This is
`CorrectionMethod Q p w`.

The limit is the start plus a correction of the form `y ᵥ* Q`, chosen so that the result
solves the balance equation. The row `y` is not unique, but `w` is. No conserved
quantity has to be found first.

The method gives the limit for every generator, by `isLimitFrom_iff_correctionMethod`.
The proof is in `LongRun.LimitEquation`.

For a process with the transition probabilities of `Q`, the same equations with its law
at time `0` as `p` give its limiting law, by
`isLimitingLaw_iff_correctionMethod`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The start plus a correction `y ᵥ* Q` that makes it solve the balance equation. -/
def CorrectionMethod (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  ∃ y : ι → ℝ, y ᵥ* (Q * Q) = -(p ᵥ* Q) ∧ w = p + y ᵥ* Q

/-- The correction method gives the limit. -/
theorem isLimitFrom_iff_correctionMethod (hQ : IsGenerator Q) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ CorrectionMethod Q p w :=
  tendsto_vecMul_transition_iff_exists hQ p w

/-! ### For a process -/

section Process

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The correction method gives the limiting law of a process,
with its law at time `0` as the start. -/
theorem isLimitingLaw_iff_correctionMethod [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ CorrectionMethod Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).trans
    (isLimitFrom_iff_correctionMethod hQ _ w)

end Process

end SympyProofs.FiniteMarkovChain
