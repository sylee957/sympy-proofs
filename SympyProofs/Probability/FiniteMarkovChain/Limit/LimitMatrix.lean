module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# Method: the limit matrix

Solve `Y * (Q * Q) = -Q` for a matrix `Y`, and take `w = p ᵥ* (1 + Y * Q)`. This is
`LimitMatrixMethod Q p w`.

The matrix `1 + Y * Q` is the limit matrix `limitMatrix Q`. It does not depend on `p`,
so it is computed once and then gives the limit from every start. The matrix `Y` is not
unique, but `1 + Y * Q` is.

The method gives the limit for every generator, by `isLimitFrom_iff_limitMatrixMethod`.

For a process with the transition probabilities of `Q`, the same equations with its law
at time `0` as `p` give its limiting law, by
`isLimitingLaw_iff_limitMatrixMethod`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The start times the limit matrix, computed as `1 + Y * Q`. -/
def LimitMatrixMethod (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  ∃ Y : Matrix ι ι ℝ, Y * (Q * Q) = -Q ∧ w = p ᵥ* (1 + Y * Q)

/-- The limit matrix method gives the limit. -/
theorem isLimitFrom_iff_limitMatrixMethod (hQ : IsGenerator Q) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ LimitMatrixMethod Q p w := by
  constructor
  · intro h
    obtain ⟨Y, hY, hL⟩ := exists_limitMatrix_eq hQ
    exact ⟨Y, hY, hL ▸ (isLimitFrom_iff_eq_vecMul_limitMatrix hQ p w).1 h⟩
  · rintro ⟨Y, hY, rfl⟩
    rw [← limitMatrix_eq_of_mul_eq hQ hY]
    exact tendsto_vecMul_transition_limitMatrix hQ p

/-! ### For a process -/

section Process

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The limit matrix method gives the limiting law of a process,
with its law at time `0` as the start. -/
theorem isLimitingLaw_iff_limitMatrixMethod [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ LimitMatrixMethod Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).trans
    (isLimitFrom_iff_limitMatrixMethod hQ _ w)

end Process

end SympyProofs.FiniteMarkovChain
