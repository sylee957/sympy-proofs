# Routh–Hurwitz algorithms and theorem statements

Import all three interfaces with:

```lean
import SympyProofs.RouthHurwitz
```

The algorithms take `Polynomial` directly. Their elimination loops and diagnostic updates are imperative; the proof-only descriptions of loop states are not additional algorithms evaluated at runtime.

## Source pointers

All Lean names below are relative to the namespace `RouthHurwitz`.

| Interface | Algorithm and result | Root-count theorem | Stability theorem |
| --- | --- | --- | --- |
| Base real-coefficient Routh | [`Imperative.run`, `Result`, `accepts`](Imperative/Basic.lean) | [`Imperative.run_signChanges_correct`](Imperative/Correctness.lean) | [`Imperative.accepts_iff_hurwitzStable`](Imperative/Correctness.lean) |
| Numeric fraction-free Routh | [`Exact.run`](Exact/Basic.lean), with the same `Imperative.Result` and `accepts` | [`Exact.run_signChanges_correct`](Exact/Correctness.lean) | [`Exact.accepts_run_iff_hurwitzStable`](Exact/Correctness.lean) |
| Parametric fraction-free Routh | [`Parametric.run`, `Result`, `Result.Holds`](Parametric/Basic.lean) | No numeric root count is returned | [`Parametric.run_correct`](Parametric/Correctness.lean) |

## Conventions and meanings

Write a nonzero input as

$$
p(s)=a_n s^n+a_{n-1}s^{n-1}+\cdots+a_0,\qquad a_n\ne0.
$$

The implementation uses `n = p.natDegree` and row width

$$
W=\left\lfloor\frac n2\right\rfloor+1.
$$

The zero polynomial also has `natDegree = 0` in Lean and is handled explicitly. All rows are fixed-length, array-backed `Vector` values. The code uses proved bounds for direct indexing. Initial coefficient reads beyond the declared degree are explicitly padded with zero.

Pseudocode conventions:

- `range(a, b)` excludes `b`; `range(b)` means `range(0, b)`.
- `indicator(P)` is `1` when `P` holds and `0` otherwise.
- Natural-number subtraction is truncated at zero. Subscripts of `coefficient` are used only after their bounds checks.
- `append` preserves the order of generated rows.
- `/` denotes field division in the base algorithm and the domain's exact-quotient operation in the FF algorithms.
- Assignments follow the displayed order. `oldLowerPivot` refers to the pivot before replacing the current row pair.

For a nonzero polynomial, let

$$
N_+(p)=\sum_{\substack{z\in\mathbb C\\p(z)=0,\ \operatorname{Re}z>0}}
\operatorname{mult}_p(z).
$$

This is the number of roots in the **open right half-plane**, counted with multiplicity. Real coefficients are interpreted in $\mathbb C$. In Lean, this is `Polynomial.rightCount` applied after the coefficient map to $\mathbb C$.

Strict Hurwitz stability means

$$
\operatorname{Stable}(p)
\iff \forall z\in\mathbb C,\quad p(z)=0\Longrightarrow\operatorname{Re}z<0.
$$

Nonzero constants are stable because they have no roots. The zero polynomial is not stable.

The numeric result has named fields `rows`, `signChanges`, and `degenerate`. Acceptance is

$$
\operatorname{Accepts}(R)
\iff \neg R.\mathrm{degenerate}\ \land\ R.\mathrm{signChanges}=0.
$$

`degenerate` records an entirely zero raw row, or the zero input. It is **not** an imaginary-axis root count and does not mean that imaginary-axis roots necessarily exist. For example, both $s^2+1$ and $s^2-1$ start with a zero odd-coefficient row; the latter has roots $\pm1$.

## Shared numeric repair

Source: [`Imperative.repair`](Imperative/Basic.lean). Both numeric algorithms use this repair. The parametric algorithm does not.

`previous` and `raw` have length `W`; `d` is the degree represented by `previous`; `w` is the active prefix length of `raw`. The Lean parameter types enforce `W > 0` and `0 <= w <= W`.

```text
REPAIR(previous, raw, d, w):
    k = 0
    while k < w and raw[k] == 0:
        k = k + 1

    if k == w:
        row = zeros(W)
        for j in range(W):
            row[j] = previous[j] * max(d - 2*j, 0)
        return (row, false)

    if raw[0] != 0:
        return (raw, true)

    row = zeros(W)
    for j in range(W):
        row[j] = raw[j]
        if j + k < w:
            row[j] = row[j] + (-1)^k * raw[j + k]
    return (row, true)
```

There are two exceptional cases:

1. **Zero pivot, nonzero row:** if the first nonzero entry is at index $k$, add a signed shift so that the new pivot is $(-1)^k\mathrm{raw}[k]\ne0$.
2. **Entirely zero active row:** replace it by the coefficients of the derivative of the polynomial represented by `previous`. This sets the degeneracy flag.

These are exact algebraic repairs. No infinitesimal symbol or floating-point perturbation is used. Their root-count effects are proved in [`Table/RootCount.lean`](Table/RootCount.lean); imaginary-axis multiplicity identities are proved in [`Table/Repairs.lean`](Table/Repairs.lean).

## 1. Base Routh algorithm

### Input, output, and pseudocode

The reference correctness theorems use $p\in\mathbb R[s]$. The generic definition can run with other field arithmetic and comparisons, but the real theorems below specify its root interpretation.

```text
BASE(p):
    n = natDegree(p)
    W = n // 2 + 1
    upper = zeros(W)
    for j in range(W):
        if 2*j <= n:
            upper[j] = coefficient(p, n - 2*j)

    if n == 0:
        return Result(
            rows = [upper],
            signChanges = 0,
            degenerate = (coefficient(p, 0) == 0))

    raw = zeros(W)
    for j in range(W):
        if 2*j + 1 <= n:
            raw[j] = coefficient(p, n - (2*j + 1))
    (lower, valid) = REPAIR(upper, raw, n, W)
    rows = [upper, lower]
    count = indicator(upper[0] / lower[0] < 0)
    degenerate = not valid

    for i in range(2, n + 1):
        w = W - i // 2
        raw = zeros(W)
        for j in range(w):
            raw[j] = (lower[0] * upper[j + 1]
                      - upper[0] * lower[j + 1]) / lower[0]
        (row, valid) = REPAIR(lower, raw, n + 1 - i, w)
        rows.append(row)
        count = count + indicator(lower[0] / row[0] < 0)
        degenerate = degenerate or not valid
        upper = lower
        lower = row

    return Result(rows = rows, signChanges = count, degenerate = degenerate)

ACCEPTS(result):
    return not result.degenerate and result.signChanges == 0
```

The counter and degeneracy flag are accumulated while producing rows. No final traversal computes acceptance or the root count.

### Correctness statements

[`Imperative.run_signChanges_correct`](Imperative/Correctness.lean), for $p\ne0$:

$$
\boxed{\mathrm{BASE}(p).\mathrm{signChanges}=N_+(p).}
$$

[`Imperative.accepts_iff_hurwitzStable`](Imperative/Correctness.lean), for every $p$:

$$
\boxed{\operatorname{Accepts}(\mathrm{BASE}(p))\iff\operatorname{Stable}(p).}
$$

The second statement includes rejection of the zero polynomial. The first deliberately assumes a nonzero polynomial.

## 2. Numeric fraction-free Routh algorithm

### Coefficient domain

`Exact.run` performs arithmetic in an ordered coefficient ring $A$. Its interface uses `CommRing`, `LinearOrder`, `IsStrictOrderedRing`, `Div`, and `MulDivCancelClass`. The last class supplies the exact-product cancellation law

$$
d\ne0\quad\Longrightarrow\quad (dq)/d=q.
$$

For root semantics, [`Exact.RealDomain`](Exact/Domain.lean) supplies a strictly monotone ring homomorphism

$$
\iota:A\hookrightarrow\mathbb R.
$$

The embedding is used by the proof, not by the runner. Integers are an example; other exact ordered domains may supply the same interface. Define $p_\iota$ by mapping each coefficient of $p$ through $\iota$.

### Pseudocode

```text
FF(p):
    n = natDegree(p)
    W = n // 2 + 1
    upper = zeros(W)
    for j in range(W):
        if 2*j <= n:
            upper[j] = coefficient(p, n - 2*j)

    if n == 0:
        return Result(
            rows = [upper],
            signChanges = 0,
            degenerate = (coefficient(p, 0) == 0))

    raw = zeros(W)
    for j in range(W):
        if 2*j + 1 <= n:
            raw[j] = coefficient(p, n - (2*j + 1))
    (lower, valid) = REPAIR(upper, raw, n, W)
    rows = [upper, lower]
    count = indicator(upper[0] * lower[0] < 0)
    degenerate = not valid
    divisor = 1
    nextDivisor = 1

    for i in range(2, n + 1):
        w = W - i // 2
        oldLowerPivot = lower[0]
        pivotSign = -1 if oldLowerPivot < 0 else 1
        raw = zeros(W)
        for j in range(w):
            numerator = pivotSign * (
                lower[0] * upper[j + 1] - upper[0] * lower[j + 1])
            raw[j] = numerator / divisor
        (row, valid) = REPAIR(lower, raw, n + 1 - i, w)

        if raw[0] == 0:
            divisor = 1
            nextDivisor = 1
        else:
            divisor = nextDivisor
            nextDivisor = abs(oldLowerPivot)

        rows.append(row)
        count = count + indicator(oldLowerPivot * row[0] < 0)
        degenerate = degenerate or not valid
        upper = lower
        lower = row

    return Result(rows = rows, signChanges = count, degenerate = degenerate)
```

Acceptance uses the same `ACCEPTS` predicate as the base algorithm. The divisor registers are delayed: within a segment without repairs, the successive divisors start with $1,1$, followed by previous pivot magnitudes. Either repair resets both registers. Every division that the runner performs is proved exact; no GCD reduction is needed.

### Correctness statements

[`Exact.run_signChanges_correct`](Exact/Correctness.lean), for $p\ne0$:

$$
\boxed{\mathrm{FF}(p).\mathrm{signChanges}=N_+(p_\iota).}
$$

[`Exact.accepts_run_iff_hurwitzStable`](Exact/Correctness.lean), for every $p$:

$$
\boxed{\operatorname{Accepts}(\mathrm{FF}(p))\iff\operatorname{Stable}(p_\iota).}
$$

Both include the exceptional repairs. They do not assume the input has only nonzero unrepaired pivots.

### Exact-division statements

For each active division, the divisor is nonzero and divides the numerator in the coefficient domain:

$$
d\ne0,\qquad d\mid N,\qquad N=dq\text{ for some }q\in A.
$$

This includes steps surrounding both kinds of repair. The full-run statements are [`FractionFree.run_exact_division` and `run_divisor_dvd_numerator`](FractionFree/Integrality.lean); [`Exact/Correctness.lean`](Exact/Correctness.lean) applies them to the coefficient-domain runner. [`FractionFree.run_preserves_ring`](FractionFree/Integrality.lean) states that the field-model rows remain in the image of the coefficient ring when the input coefficients do.

## 3. Parametric fraction-free stability certificate

### Input and interpretation

Here $p\in A[s]$ and $A$ is an integral domain with decidable equality and exact division (`CommRing`, `IsDomain`, `DecidableEq`, `Div`, and `MulDivCancelClass`). Examples include $\mathbb Z[t]$ and suitable multivariate polynomial rings. No order or sign test on $A$ is required.

A specialization is any ring homomorphism $f:A\to\mathbb R$. It need not be injective: a nonzero parameter expression may specialize to zero. Write $p_f$ for coefficientwise specialization.

The result has named fields:

- `rows`: the generated fixed-width symbolic rows;
- `positive`: the expressions required to be strictly positive after specialization.

[`Parametric.Result.Holds`](Parametric/Basic.lean) interprets the result as

$$
\operatorname{Holds}(R,f)
\iff \bigwedge_{b\in R.\mathrm{positive}}f(b)>0.
$$

### Pseudocode

```text
PARAMETRIC(p):
    n = natDegree(p)
    a = leadingCoefficient(p)
    W = n // 2 + 1
    if n == 0:
        return Result(rows = [[a*a]], positive = [a*a])

    upper = zeros(W)
    lower = zeros(W)
    for j in range(W):
        if 2*j <= n:
            upper[j] = a * coefficient(p, n - 2*j)
        if 2*j + 1 <= n:
            lower[j] = a * coefficient(p, n - (2*j + 1))

    pivots = [lower[0]]
    rows = [upper, lower]
    divisor = 1
    nextDivisor = 1
    for _ in range(n - 1):
        if lower[0] != 0:
            row = zeros(W)
            for j in range(W - 1):
                row[j] = (lower[0] * upper[j + 1]
                          - upper[0] * lower[j + 1]) / divisor
            divisor = nextDivisor
            nextDivisor = lower[0]
            pivots.append(row[0])
            rows.append(row)
            upper = lower
            lower = row

    return Result(rows = rows, positive = [a*a] + pivots)
```

This is a single pass at the input's declared degree. It uses signed divisors and no repairs or absolute values. When a symbolic pivot becomes zero, it remains in the certificate and subsequent iterations do no arithmetic. The positivity condition then fails at every specialization.

The initial rows belong to $q=a_np$, whose specialized leading coefficient is $f(a_n)^2$. This permits either sign of $f(a_n)$ without a symbolic sign decision. [`Parametric.run_positive_eq_firstColumn`](Parametric/Invariant.lean) proves that `positive` is exactly the first column of `rows`; the list is accumulated during execution.

### Correctness statement

[`Parametric.run_correct`](Parametric/Correctness.lean), for every specialization $f:A\to\mathbb R$:

$$
\boxed{
\operatorname{Holds}(\mathrm{PARAMETRIC}(p),f)
\iff f(a_n)\ne0\ \land\ \operatorname{Stable}(p_f).
}
$$

The leading-coefficient guard is essential. For instance, $p(s,t)=ts+1$ becomes the stable constant $1$ at $t=0$, but its declared-degree certificate is false there. The algorithm does not branch into separate certificates for lower-degree specializations.

For a parameter region with assumptions $H(f)$, if

$$
H(f)\Longrightarrow f(a_n)\ne0,
$$

then, under $H(f)$, the generated inequalities are equivalent to stability. To certify the whole region, prove

$$
\forall f,\quad H(f)\Longrightarrow
\left(f(a_n)\ne0\ \land\
\bigwedge_{b\in\mathrm{PARAMETRIC}(p).\mathrm{positive}}f(b)>0\right).
$$

The interface returns a condition, not a Boolean stability decision or a numeric root count. Simplifying the inequalities or proving them on a region is a subsequent mathematical task.

### Supporting theorem statements

[`Parametric.run_exact_division`](Parametric/Invariant.lean) states that at every taken loop branch the divisor is nonzero and divides each elimination numerator in $A$. It requires no ordering or real specialization.

[`Parametric.run_positive_eq_firstColumn`](Parametric/Invariant.lean) states that the returned `positive` list is exactly the first column of the returned `rows`.

For a degree-$n$ polynomial $q(s)=\sum_{i=0}^n b_i s^i$, put $b_i=0$ outside $0\le i\le n$. Define the Hurwitz matrix and its leading minors by

$$
H(q)_{ij}=b_{n+i-2j}\quad(1\le i,j\le n),
\qquad
\Delta_k(q)=\det H(q)_{1\le i,j\le k}.
$$

[`Arithmetic.hurwitzStable_iff_minors`](FractionFree/Stability.lean) states that, when $\deg q=n$ and $b_n>0$,

$$
\boxed{\operatorname{Stable}(q)
\iff \bigwedge_{k=1}^{n}\Delta_k(q)>0.}
$$

The formal definition `hurwitzMinor q n k` keeps the declared degree $n$ explicit. [`Arithmetic.hurwitzMinor_map`](FractionFree/Stability.lean) states that for any coefficient ring homomorphism $f$, with the same declared degree on both sides,

$$
f(\Delta_k(q))=\Delta_k(q_f).
$$

No injectivity or nonzero-pivot assumption is required for this specialization identity.

## Implementation boundaries

The exact-division polynomial instances in [`Exact/Polynomial.lean`](Exact/Polynomial.lean) are enabled with:

```lean
open scoped RouthHurwitz.Exact
```

They use leading-term cancellation and support suitable iterated and finite multivariate polynomial rings. Mathlib field-coefficient division retains priority. Mathlib's polynomial arithmetic is noncomputable for code extraction, so these instances carry that annotation; the generic runners can execute when supplied with executable coefficient arithmetic.

The pseudocode describes the verified Lean loops, but a translation into another language still needs a correspondence proof. Root statements assume exact arithmetic. The numeric `degenerate` flag is not an axis-root counter, and the parametric interface has no root-count result. No benchmark or time-complexity claim is part of this guide.
