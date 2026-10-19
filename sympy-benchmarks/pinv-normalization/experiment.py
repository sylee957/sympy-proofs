"""Research prototype: remove the known pivot factor from a skeleton pseudoinverse.

Scope: polynomial matrices over QQ(i) in real parameters, with a supplied
generically nonsingular minor of order equal to the generic rank. This is not
a production pinv implementation or a claim of a new mathematical identity.

Run from the sympy-proofs directory:
    .venv-jordan/bin/python sympy-benchmarks/pinv-normalization/experiment.py
"""

from itertools import combinations
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "sympy"))

import sympy as s
from sympy.polys.matrices import DomainMatrix


def expanded(M):
    return M.applyfunc(s.expand)


def faddeev_det_adjugate(H):
    """Polynomial computation; divides only by the fixed integers 1,...,r."""
    r = H.rows
    assert r == H.cols and r > 0
    F = s.eye(r)
    for k in range(1, r + 1):
        HF = expanded(H * F)
        e = s.expand(s.trace(HF) / k)
        if k == r:
            return e, F
        F = expanded(e * s.eye(r) - HF)


def fraction_free_det_adjugate(H, parameters):
    """Cubic-count elimination backend with unit-cost arithmetic/exact quotients.

    inv_den may return a reduced pair. Restore the actual adjugate using the
    determinant and an exact scalar quotient; no rational-function division.
    """
    domain = s.QQ_I.poly_ring(*parameters)
    dm = DomainMatrix.from_Matrix(H).convert_to(domain).to_dense()
    determinant = dm.det()
    numerator, denominator = dm.inv_den(method="rref")
    scale = domain.exquo(determinant, denominator)
    adjugate = numerator.scalarmul(scale)
    return domain.to_sympy(determinant), adjugate.to_Matrix()


def normalized_skeleton(A, rows, cols, parameters, backend="faddeev"):
    """Return polynomial N,S,q with A^+ = N/S on the generic-rank locus.

    Preconditions: entries are polynomials in real parameters over QQ(i),
    len(rows) == len(cols) == rank(A) over the fraction field, and the
    selected minor is nonzero as a polynomial. Lower-rank specializations
    must be treated separately. Exact division happens before evaluation.
    """
    assert parameters and all(x.is_real for x in parameters)
    assert len(rows) == len(cols) > 0
    C = A.extract(range(A.rows), cols)
    R = A.extract(rows, range(A.cols))
    W = A.extract(rows, cols)
    domain = s.QQ_I.poly_ring(*parameters)
    Wdm = DomainMatrix.from_Matrix(W).convert_to(domain).to_dense()
    p = s.expand(domain.to_sympy(Wdm.det()))
    if p == 0:
        raise ValueError("The selected minor vanishes identically")
    # Single rank-sized core. It need not be Hermitian.
    K = expanded(C.H * A * R.H)
    if backend == "faddeev":
        raw_D, adjK = faddeev_det_adjugate(K)
    elif backend == "fraction_free":
        raw_D, adjK = fraction_free_det_adjugate(K, parameters)
    else:
        raise ValueError("Unknown backend")
    raw_N = expanded(R.H * adjK * C.H)
    q = s.expand(s.conjugate(p))

    # No gcd search or rational simplification: divide by the prescribed q.
    divisor = s.Poly(q, *parameters, domain=s.QQ_I)

    def quotient(f):
        return s.Poly(f, *parameters, domain=s.QQ_I).exquo(divisor).as_expr()

    return raw_N.applyfunc(quotient), quotient(raw_D), q


def faddeev_numerator(A, r):
    """Independent ambient-size reference N=F_(r-1)(A.H*A)*A.H, S=e_r."""
    G = expanded(A.H * A)
    F = s.eye(A.cols)
    for k in range(1, r + 1):
        GF = expanded(G * F)
        e = s.expand(s.trace(GF) / k)
        if k == r:
            return expanded(F * A.H), e
        F = expanded(e * s.eye(A.cols) - GF)


def assert_zero(M):
    assert all(s.cancel(x) == 0 for x in M)


def verify_case(name, A, rows, cols, parameters, specializations=()):
    N, S, q = normalized_skeleton(A, rows, cols, parameters)
    ff_N, ff_S, _ = normalized_skeleton(A, rows, cols, parameters,
                                       backend="fraction_free")
    assert_zero(N - ff_N)
    assert s.expand(S - ff_S) == 0
    r = len(rows)
    ref_N, ref_S = faddeev_numerator(A, r)
    assert_zero(N - ref_N)
    assert s.expand(S - ref_S) == 0

    # Independent Cauchy-Binet denominator check, only on these small cases.
    sum_minors = 0
    for I in combinations(range(A.rows), r):
        for J in combinations(range(A.cols), r):
            minor = A.extract(I, J).det()
            sum_minors += minor * s.conjugate(minor)
    assert s.expand(S - sum_minors) == 0

    # All four Penrose identities, with denominators cleared.
    assert_zero(A * N * A - S * A)
    assert_zero(N * A * N - S * N)
    assert_zero((A * N).H - A * N)
    assert_zero((N * A).H - N * A)
    assert s.expand(s.conjugate(S) - S) == 0

    boundary_count = 0
    for point in specializations:
        A0, S0 = A.subs(point), S.subs(point)
        if A0.rank() == r:
            assert S0 != 0
            assert_zero(N.subs(point) / S0 - A0.pinv())
            boundary_count += q.subs(point) == 0
        else:
            assert S0 == 0

    print(f"PASS {name}: shape={A.shape}, rank={r}, "
          f"pivot_factor={s.factor(q)}, preserved-rank pivot zeros={boundary_count}")
    return N, S, q


def main():
    t, u = s.symbols("t u", real=True)
    cases = []
    cases.append(("rank_one", s.Matrix([[t, 1], [2*t, 2]]), [0], [0], (t,),
                  [{t: 0}, {t: 1}]))
    B = s.Matrix([[t, 0], [0, 1], [1, 1]])
    C = s.Matrix([[1, 0, u, 1], [0, 1, 1, u]])
    cases.append(("rank_two", B*C, [0, 1], [0, 1], (t, u),
                  [{t: 0, u: 0}, {t: 0, u: 2}, {t: 2, u: -1}]))
    Bc = s.Matrix([[t+s.I*u, 0], [0, 1], [1+s.I, 1]])
    Cc = s.Matrix([[1, 0, s.I*u], [0, 1, 1+s.I*u]])
    cases.append(("complex_rank_two", Bc*Cc, [0, 1], [0, 1], (t, u),
                  [{t: 0, u: 0}, {t: 0, u: 1}, {t: 1, u: 2}]))
    cases.append(("genuine_rank_drop", s.diag(1, t), [0, 1], [0, 1], (t,),
                  [{t: 0}, {t: 1}]))
    cases.append(("nonmonomial_pivot", s.Matrix([[(t-u)*(t+u), 1],
                                                [2*(t-u)*(t+u), 2]]),
                  [0], [0], (t, u), [{t: 1, u: 1}, {t: 1, u: -1}]))

    rng = random.Random(714)
    for k in range(8):
        r = 1 + k % 3
        m, n = r + 1, r + 2
        left_top = s.diag(t, *([1] * (r - 1)))
        left_bottom = s.Matrix([[1] + [rng.randint(-2, 2) for _ in range(r - 1)]])
        left = left_top.col_join(left_bottom)
        right = s.eye(r).row_join(s.Matrix(r, 2,
            lambda i, j: rng.randint(-2, 2) + rng.randint(-1, 1)*u))
        cases.append((f"seeded_{k}", left*right, list(range(r)), list(range(r)),
                      (t, u), [{t: 0, u: -1}, {t: 0, u: 2}, {t: 1, u: 1}]))

    for case in cases:
        verify_case(*case)

    # Changing the selected minor gives exactly the same polynomial pair.
    A = cases[1][1]
    N0, S0, _ = normalized_skeleton(A, [0, 1], [0, 1], (t, u))
    for rows, cols in [([1, 2], [0, 1]), ([0, 2], [1, 2]), ([1, 2], [2, 3])]:
        N, S, _ = normalized_skeleton(A, rows, cols, (t, u))
        assert_zero(N - N0)
        assert s.expand(S - S0) == 0
    print("PASS pivot independence: 4 distinct row/column selections")
    print(f"All {len(cases)} cases passed with both backends; "
          "exact quotients and ambient Faddeev equality verified.")


if __name__ == "__main__":
    main()
