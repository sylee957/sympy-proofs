module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# Method: the balance equation with conserved quantities

Solve `w ᵥ* Q = 0` together with `w ⬝ᵥ h = p ⬝ᵥ h` for every column `h` with
`Q *ᵥ h = 0`. This is `ConservedMethod Q p w`.

A column `h` with `Q *ᵥ h = 0` is a conserved quantity: its average under the law of
the chain never changes. The column of all ones is one, and for it the equation says
that `w` has the same total mass as `p`. So this method is the balance method with one
more equation for each further independent conserved quantity.

The method gives the limit for every generator, by `isLimitFrom_iff_conservedMethod`.
The proof is in `LongRun.LimitEquation`.

For a process with the transition probabilities of `Q`, the same equations with its law
at time `0` as `p` give its limiting law, by
`isLimitingLaw_iff_conservedMethod`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The balance equation, with the value of the start on every conserved column. -/
def ConservedMethod (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  w ᵥ* Q = 0 ∧ ∀ h : ι → ℝ, Q *ᵥ h = 0 → w ⬝ᵥ h = p ⬝ᵥ h

/-- The method of conserved quantities gives the limit. -/
theorem isLimitFrom_iff_conservedMethod (hQ : IsGenerator Q) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ ConservedMethod Q p w :=
  tendsto_vecMul_transition_iff_forall_dotProduct hQ p w

/-! ### For a process -/

section Process

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The method of conserved quantities gives the limiting law of a process,
with its law at time `0` as the start. -/
theorem isLimitingLaw_iff_conservedMethod [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ ConservedMethod Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).trans
    (isLimitFrom_iff_conservedMethod hQ _ w)

end Process

end SympyProofs.FiniteMarkovChain
