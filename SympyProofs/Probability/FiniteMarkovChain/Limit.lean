import SympyProofs.Probability.FiniteMarkovChain.Limit.Balance
import SympyProofs.Probability.FiniteMarkovChain.Limit.JumpChain
import SympyProofs.Probability.FiniteMarkovChain.Limit.Conserved
import SympyProofs.Probability.FiniteMarkovChain.Limit.Correction
import SympyProofs.Probability.FiniteMarkovChain.Limit.LimitMatrix

/-!
# Methods to compute the limit

This folder lists the ways to compute where a chain with generator `Q` goes in the long
run, started from a row `p`. Every method has the same shape.

`LongRun.MatrixLimiting` fixes what is computed. `IsLimitFrom Q p w` says that the
row `p ᵥ* transition Q t` tends to `w`. That is the definition, with a limit in it. For
a process it means this: the limiting law of a process is the limit from its law at
time `0`, by `isLimitingLaw_iff_isLimitFrom` in `LongRun.ProcessLimiting`.

Each file gives one method. A method is a statement `Method Q p w` with no limit
and no matrix exponential in it, only linear equations. With it come two theorems,
under the condition that the method needs.

* `IsLimitFrom Q p w ↔ Method Q p w`, for matrices.
* `IsLimitingLaw X P w ↔ Method Q p₀ w`, for a process with the transition
  probabilities of `Q`, where `p₀` is its law at time `0`.

The methods are these.

* `Balance`: `BalanceMethod`. Solve `w ᵥ* Q = 0` with the total mass of `p`. It needs
  that some state can be reached from every state.
* `JumpChain`: `JumpChainMethod`. Solve `π ᵥ* jumpMatrix Q = π` for the jump chain and
  divide by the exit rates. It has the same solutions as the balance method and needs
  the same condition.
* `Conserved`: `ConservedMethod`. Solve `w ᵥ* Q = 0` with `w ⬝ᵥ h = p ⬝ᵥ h` for every
  column `h` with `Q *ᵥ h = 0`. It needs no condition.
* `Correction`: `CorrectionMethod`. Solve `y ᵥ* (Q * Q) = -(p ᵥ* Q)` and take
  `w = p + y ᵥ* Q`. It needs no condition.
* `LimitMatrix`: `LimitMatrixMethod`. Solve `Y * (Q * Q) = -Q` and take
  `w = p ᵥ* (1 + Y * Q)`. It needs no condition, and its matrix serves every start.

The proofs of the last three methods are in `LongRun.LimitEquation`. This folder states
them in one common form.
-/
