module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# A process as one object

Most statements in this folder take a process loose: a family `X` of random variables
and a measure `P`, with the probability space `Ω` in the background. That is the form
that is easiest to apply.

Some statements say "some process" or "every process", on any probability space. They
have to bind the space, its measurable sets, the measure, and the family, each time.
`Process ι` is these four as one object, so that such a statement binds one thing.

`Process ι` assumes nothing about how the process moves. A statement adds what it
needs, such as `IsHomogeneousMarkovProcess S.X S.P`, as a condition on `S.X` and `S.P`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory
open scoped NNReal

universe u

/-- A process with states in `ι`: a probability space and the state at each time.
Nothing is assumed about how the process moves. -/
structure Process (ι : Type u) where
  /-- The sample space. -/
  Ω : Type u
  /-- The measurable sets of the sample space. -/
  [measurableSpace : MeasurableSpace Ω]
  /-- The probability measure. -/
  P : Measure Ω
  /-- The measure has total mass one. -/
  [isProbabilityMeasure : IsProbabilityMeasure P]
  /-- The state at each time. -/
  X : ℝ≥0 → Ω → ι

attribute [instance] Process.measurableSpace Process.isProbabilityMeasure

end SympyProofs.FiniteMarkovChain
