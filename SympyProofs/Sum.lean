module

public import SympyProofs.Sum.Gosper
public import SympyProofs.Sum.ModularShifts
public import SympyProofs.Sum.PolynomialSum
public import SympyProofs.Sum.ShiftlessDecomposition
public import SympyProofs.Sum.RationalSum

/-!
# Summation algorithms

The library contains Gosper's hypergeometric summation algorithm, polynomial
summation, rational summation, shiftless decomposition, and modular shift enumeration.
`SympyProofs.Sum.Gosper` provides the Gosper theorem, executable algorithm model,
and soundness and completeness proofs.

`PolynomialSum.antidifference` handles polynomial summands directly over any
commutative rational algebra, including polynomial parameter rings. It generates
and accumulates one monomial primitive row at a time using the rational coefficient
recurrence. Bernoulli polynomials occur only in the proof specification.
The proofs establish the difference identity, a degree bound, finite sums, and
compatibility with every parameter specialization. `PolynomialSum.antidifference_sound`
proves that the computed output has
the required difference and vanishes at zero. The implementation and proofs live
in `PolynomialSum.Algorithm` and `PolynomialSum.Correctness`. The algorithm uses
no candidate search or parameter-dependent division. The coefficient recurrence
uses no parameter zero tests; the polynomial interface obtains its input degree.

`ShiftlessDecomposition.decompose` constructs shiftless decompositions
over any characteristic-zero field with decidable equality, using supplied gcd,
derivative, and complete integer-shift enumeration. Division uses polynomial
operators. `ModularShifts` implements modular shift enumeration over ℚ.
Layer reconstruction and maximal multiplicity are proved;
`decompose_sound` and `decompose_complete` prove full correctness and successful
construction for every nonzero input. The function returns a decomposition
directly; primitive contracts and the nonzero-input assumption occur only in
the correctness theorems.
-/
