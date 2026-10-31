module

public import SympyProofs.Gosper.Hypergeometric
public import SympyProofs.Gosper.Nonsummable
public import SympyProofs.Gosper.Applications
public import SympyProofs.Gosper.Binomial
public import SympyProofs.Gosper.Cubic
public import SympyProofs.Gosper.Algorithm
public import SympyProofs.Gosper.PolynomialSum
public import SympyProofs.Gosper.ShiftlessDecomposition
public import SympyProofs.Gosper.ModularShifts
public import SympyProofs.Gosper.RationalSum

/-!
# Gosper's indefinite hypergeometric summation theorem

Formalization of R. W. Gosper, *Decision procedure for indefinite hypergeometric
summation*, PNAS 75 (1978), 40–42, DOI: 10.1073/pnas.75.1.40.

The main theorem is `Gosper.hypergeometric_gosper_criterion`. Normalization is
provided by `Gosper.exists_normalForm`; `Gosper.exists_normalized_criterion`
combines normalization and the finite linear-system reduction. Numerical
finite sums follow from `Gosper.certificate_sum` and the product-sum theorems.

`Algorithm.gosperTerm` models the procedure on Mathlib polynomials over a
characteristic-zero coefficient field with decidable `IsLocalization.IsInteger ℤ`
membership. `Encodable.choose` recovers integer witnesses constructively; a rational
instance decides membership by checking the reduced denominator. A `Backend`
supplies factorization, resultant, zero matrices, entry updates, column reads, and RREF;
shift resultants, natural integer roots, and linear solving
are derived from them. Gcd and translation remain Mathlib operations. Ordinary
and fraction-free RREF use the same matrix/denominator/pivots contract.
`referenceBackend rref` supplies Mathlib factorization and resultant with the
given RREF operation. The degree bound is unchanged.
`Algorithm.gosperTerm_complete` proves that any backend satisfying `Backend.Valid`
succeeds exactly when a hypergeometric antidifference exists;
`Algorithm.gosperTerm_none_iff` certifies
nonsummability under explicit nonzero-input hypotheses. The algorithm returns
`Option Certificate` without proof arguments or an error branch. The returned
certificate gives finite sums via `Algorithm.gosperTerm_sum`, with explicit
denominator conditions on the summation interval. Mathlib's noncomputable
operations keep this a mathematical algorithm model.

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
