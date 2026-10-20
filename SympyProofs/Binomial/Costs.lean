module

public import SympyProofs.Binomial.Costs.FullAsymptotics

/-!
# Binomial cost analysis

Algorithm-specific instrumentation and bounds live in this directory. Reusable
Python operation models and composition rules live in `SympyProofs.Python.Cost`.
`FullAsymptotics` proves a uniform quadratic upper bound on the actual complete
`primeExponentsM` counter under the declared schoolbook policy. The proof includes
the lazy sieve, integer arithmetic, allocation payload, product tree and shift.
-/
