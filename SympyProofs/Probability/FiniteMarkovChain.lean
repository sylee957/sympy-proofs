import SympyProofs.Probability.FiniteMarkovChain.Matrix
import SympyProofs.Probability.FiniteMarkovChain.Process
import SympyProofs.Probability.FiniteMarkovChain.LongRun
import SympyProofs.Probability.FiniteMarkovChain.PathMeasure
import SympyProofs.Probability.FiniteMarkovChain.Limit

/-!
# Finite-state continuous-time Markov chain stationarity

The development has five parts.

`Matrix` is about matrices only: generators, their transition matrices, and which
states can be reached from which.

`Process` is about a process on a probability space: what a time-homogeneous Markov
process is, and that it has a generator.

`LongRun` holds the stationary and the limiting distribution of a generator, and
the stationary and the limiting law of a process, with the theorems that link the
four.

`PathMeasure` constructs a measure on the space of paths, and so shows that every
generator has a time-homogeneous Markov process with its transition probabilities. It
also shows that this measure is the only one for a given initial distribution, and
that the limiting laws of all the processes of a generator are exactly its stationary
distributions.

`Limit` lists the ways to compute the limit of a chain from a given start, each
in the same form: a system of linear equations and a theorem that its solution is the
limit.

The motivation is SymPy issue #30980 and PR #30981, which change the stationary
condition of a continuous-time chain from `w * Q = w` to `w * Q = 0`. The second
equation is `Balance Q w` in `LongRun.MatrixStationary`. This development proves
that it is the condition for a process to keep its law, and that, when some state can
be reached from every state, its one solution of total mass one is the limit of the law
of the process from every start.

https://github.com/sympy/sympy/issues/30980
https://github.com/sympy/sympy/pull/30981
-/
