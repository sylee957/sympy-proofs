import SympyProofs.Probability.FiniteMarkovChain.LongRun.MatrixStationary
import SympyProofs.Probability.FiniteMarkovChain.LongRun.Convergence
import SympyProofs.Probability.FiniteMarkovChain.LongRun.LimitMatrix
import SympyProofs.Probability.FiniteMarkovChain.LongRun.LimitEquation
import SympyProofs.Probability.FiniteMarkovChain.LongRun.MatrixLimiting
import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessStationary
import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# The long run of a chain: stationary and limiting distributions

This folder holds the two long-run notions of a chain, each on two levels.

The matrix level is about a generator `Q` and rows of numbers. No probability space
appears in it. Its notions are called distributions, as in textbooks, where they belong
to the chain. The process level is about one process `X` on one probability space
`(Ω, P)`. Its notions are called laws.

* `MatrixStationary`: `IsStationaryDistribution Q w`. The row `w` is a distribution and
  solves the balance equation `w ᵥ* Q = 0`.
* `MatrixLimiting`: `IsLimitingDistribution Q w`. From every state, the probability of
  being in state `j` tends to `w j`. The file also has `IsLimitFrom Q p w`, the limit
  from one given start `p`.
* `ProcessStationary`: `IsStationaryLaw X P w`. The state of the process has the law
  `w` at every time.
* `ProcessLimiting`: `IsLimitingLaw X P w`. The law of the state of the process tends
  to `w`.

The four notions are linked as follows. Take a process with the transition
probabilities of `Q`.

* Stationary, process and matrix: the process has the stationary law `w` exactly when
  it starts from `w` and `w` solves the balance equation, by `isStationaryLaw_iff`.
* Limiting, process and matrix: the limiting law of the process is the limit from its
  law at time `0`, by `isLimitingLaw_iff_isLimitFrom`. If `Q` has a limiting
  distribution, it is the limiting law of every process, by
  `IsLimitingDistribution.isLimitingLaw`.
* Matrix, limiting and stationary: a limiting distribution is a stationary distribution,
  and a stationary distribution is the limiting distribution when some state can be
  reached from every state, by `isLimitingDistribution_iff`.
* Process, stationary and limiting: a stationary law is the limiting law, by
  `IsStationaryLaw.isLimitingLaw`, and a limiting law is a stationary distribution of
  `Q`, by `IsLimitingLaw.isStationaryDistribution`.

These links start from a given process. The other direction, from the matrix to its
processes, needs a process to exist, and so it is in `PathMeasure.Limit`: a stationary
distribution is the stationary law of some process, and a limiting distribution is the
limiting law of every process.

What always exists and what does not: a generator always has a stationary
distribution, and a process always has exactly one limiting law. A generator has a
limiting distribution exactly when some state can be reached from every state, and
that is also exactly when its stationary distribution is unique.

Three more files hold the proofs for the matrix level. `Convergence` proves that a
stationary distribution exists, when it is unique, and that the transition matrices
converge. `LimitMatrix` names their limit, `limitMatrix Q`. `LimitEquation` gives
linear equations that determine the limit from a start.
-/
