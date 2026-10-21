module

public import SympyProofs.Gosper.Hypergeometric
public import SympyProofs.Gosper.Nonsummable
public import SympyProofs.Gosper.Applications
public import SympyProofs.Gosper.Binomial
public import SympyProofs.Gosper.Cubic

/-!
# Gosper's indefinite hypergeometric summation theorem

Formalization of R. W. Gosper, *Decision procedure for indefinite hypergeometric
summation*, PNAS 75 (1978), 40–42, DOI: 10.1073/pnas.75.1.40.

The main theorem is `Gosper.hypergeometric_gosper_criterion`. Normalization is
provided by `Gosper.exists_normalForm`; `Gosper.exists_normalized_criterion`
combines normalization and the finite linear-system reduction. Numerical
finite sums follow from `Gosper.certificate_sum` and the product-sum theorems.

This formalizes the mathematical decision criterion, rather than an executable
CAS implementation.
-/
