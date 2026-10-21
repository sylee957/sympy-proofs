module

public import SympyProofs.Gosper.Hypergeometric
public import SympyProofs.Gosper.Nonsummable
public import SympyProofs.Gosper.Applications
public import SympyProofs.Gosper.Binomial
public import SympyProofs.Gosper.Cubic
public import SympyProofs.Gosper.Algorithm
public import SympyProofs.Gosper.Algorithm.Correctness
public import SympyProofs.Gosper.Algorithm.Completeness
public import SympyProofs.Gosper.Algorithm.Examples

/-!
# Gosper's indefinite hypergeometric summation theorem

Formalization of R. W. Gosper, *Decision procedure for indefinite hypergeometric
summation*, PNAS 75 (1978), 40–42, DOI: 10.1073/pnas.75.1.40.

The main theorem is `Gosper.hypergeometric_gosper_criterion`. Normalization is
provided by `Gosper.exists_normalForm`; `Gosper.exists_normalized_criterion`
combines normalization and the finite linear-system reduction. Numerical
finite sums follow from `Gosper.certificate_sum` and the product-sum theorems.

`Algorithm.gosperTerm` models the procedure on Mathlib polynomials over a
characteristic-zero coefficient field. It uses Mathlib resultant/gcd operations,
the proved paper degree bound, and explicit row reduction on field-valued
matrices. `Algorithm.gosperTerm_complete` proves that it succeeds exactly when a
hypergeometric antidifference exists; `Algorithm.gosperTerm_none_iff` certifies
nonsummability under explicit nonzero-input hypotheses. The algorithm returns
`Option Certificate` without proof arguments or an error branch. The returned
certificate gives finite sums via `Algorithm.gosperTerm_sum`, with explicit
denominator conditions on the summation interval. Mathlib's noncomputable
operations keep this a mathematical algorithm model.
-/
