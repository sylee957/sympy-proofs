module

public import SympyProofs.Probability.FiniteMarkovChain.Process.MarkovProperty
public import SympyProofs.Probability.FiniteMarkovChain.Process.Homogeneous
public import SympyProofs.Probability.FiniteMarkovChain.Process.Continuous
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Time-homogeneous Markov processes

A process is a family `X t : Ω → ι` of random variables on a probability space
`(Ω, P)`. `IsHomogeneousMarkovProcess X P` says that it is a time-homogeneous Markov
process. The definition mentions no matrix and no measure on paths.

The process is measurable, so each `X t` is a random variable. Beyond that the
definition has three parts: the Markov property, time homogeneity, and that the process
never leaves its current state instantly. Each is written as a product and not as a
conditional probability. Homogeneity compares any two times and continuity holds at
every time, so a state is tested at whatever time the process can be in it.

The three parts are `MarkovPropertyProduct` from `MarkovProperty`, `HomogeneousProduct`
from `Homogeneous`, and `ContinuousProduct` from `Continuous`. Those files also state
each property with conditional probabilities and prove that the forms are equivalent.

`Transition` says what it means for a matrix to give the transition probabilities of a
process, and `Generator` proves that such a matrix exists. Generators and transition
matrices themselves are defined in `Matrix.Generator`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open MeasureTheory
open scoped NNReal

variable {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]

/-- `X` is a time-homogeneous Markov process on the probability space `(Ω, P)`. No
matrix is mentioned. Every condition is written as a product and not as a conditional
probability, so it also makes sense for events of probability zero. -/
structure IsHomogeneousMarkovProcess (X : ℝ≥0 → Ω → ι) (P : Measure Ω) : Prop where
  /-- The state at each time is a random variable. -/
  measurable : ∀ t, Measurable (X t)
  /-- Markov property: given the state `i` at time `s`, the state at a later time `t`
  does not depend on the states at finitely many earlier times. -/
  markov : MarkovPropertyProduct X P
  /-- Time homogeneity: the chance of moving from `i` to `j` over a duration `h` is
  the same from any two times `s` and `s'`. -/
  homogeneous : HomogeneousProduct X P
  /-- At no time does the process leave its current state instantly. -/
  continuous : ContinuousProduct X P

end SympyProofs.FiniteMarkovChain
