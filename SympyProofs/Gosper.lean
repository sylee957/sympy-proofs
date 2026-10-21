module

public import SympyProofs.Gosper.Hypergeometric
public import SympyProofs.Gosper.Nonsummable
public import SympyProofs.Gosper.Applications
public import SympyProofs.Gosper.Binomial
public import SympyProofs.Gosper.Cubic
public import SympyProofs.Gosper.Algorithm

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
-/
