Rank decomposition with a prescribed cancellation of pivot factors

Status: algebraic derivation and an executable SymPy research prototype.
The underlying skeleton and fraction-free pseudoinverse formulas are known.
Novelty of this particular normalization/implementation has not been established.
This extension has not yet been formalized in Lean or benchmarked for speed.

Assumptions

A(x) is an m-by-n polynomial matrix over the reals or complexes in real
parameters x. Conjugation fixes the parameters. Its rank over the rational
function field is r > 0. Choose row indices I and column indices J of size r
such that p = det(A[I,J]) is not the zero polynomial. The selected minor may
vanish at special parameter values, even when rank(A) remains r.

Construction

  C = A[:,J],  R = A[I,:],  W = A[I,J],  p = det(W)
  K = C.H * A * R.H                          (an r-by-r polynomial matrix)
  D = det(K)
  M = R.H * adj(K) * C.H
  S = exquo(D, conjugate(p))
  N = entrywise_exquo(M, conjugate(p))

Return the polynomial pair (N, S), representing A.pinv() = N/S on the locus
rank(A) = r. Here exquo is exact polynomial division, not pointwise division
or a generic rational simplifier. Perform these divisions BEFORE substituting
parameter values. No polynomial gcd or factorization is needed for them.

Proof and connection to Faddeev

Over the rational function field, the skeleton identity is A = C W^-1 R.
Set P = C.H*C and Q = R*R.H. Then K = P W^-1 Q and

  A^+ = R.H Q^-1 W P^-1 C.H = R.H K^-1 C.H = M/D.

Define the intrinsic polynomial

  S_r(A) = sum_{|U|=|V|=r} |det(A[U,V])|^2.

Cauchy-Binet applied to the skeleton factorization gives

  det(P) det(Q) = |p|^2 S_r(A),
  D = det(P) det(Q) / p = conjugate(p) S_r(A).

For G = A.H*A, write F_0 = I and

  e_k = trace(G F_{k-1})/k,
  F_k = e_k I - G F_{k-1}.

The rank-r Faddeev formula is A^+ = N_r(A)/e_r(G), where
N_r(A) = F_{r-1}(G) A.H and e_r(G) = S_r(A). Both N_r and S_r are
polynomials in the input entries and their conjugates. Consequently

  M = conjugate(p) N_r(A)

as a polynomial identity: it holds in the rational function field, and the
polynomial ring embeds in that field. Thus BOTH prescribed quotients exist
in the polynomial ring. They recover exactly N_r(A) and S_r(A), independent
of the selected I,J, without forming the ambient Gram matrix or enumerating
its minors.

At every real parameter value with rank(A) = r, S_r(A) > 0. Thus N/S remains
valid when p = 0 but rank is preserved. At actual rank drops S_r(A) = 0 and
the lower-rank pseudoinverse requires a separate branch. The zero matrix is
a separate rank-zero branch. For rational input, clear entry denominators
first and restrict to parameter values where the input is defined.

Computational implications

The determinant/adjugate backend acts on ONE r-by-r matrix, rather than an
ambient-size Gram matrix. Choices include:

  ordinary Faddeev:        O(m*n*r + r^4) arithmetic operations;
  blocked Faddeev:         O(m*n*r + r^3.5) with ordinary multiplication;
  fraction-free methods:  O(m*n*r + r^3) arithmetic/exact-quotient operations.

These are unit-operation counts, not bit complexity or symbolic timing bounds.
Polynomial multiplication and exact division have degree-dependent costs.
Selecting the minor by rank-revealing elimination also fits a standard
O(m*n*r) arithmetic count. The prototype takes that selection as input.

The prototype provides ordinary Faddeev and fraction-free DomainMatrix
backends. For the latter, inv_den may return a reduced numerator/denominator
pair; we restore the actual adjugate by multiplying its numerator by the exact
quotient det(K)/denominator. The final normalization must use the determinant,
not an arbitrary reduced denominator, to guarantee divisibility by conjugate(p).

If entries of A have total degree <= delta, the unreduced core determinant
has degree <= 3*r*delta and M has degree <= (3*r-1)*delta. The normalized
pair satisfies degree(S) <= 2*r*delta and degree(N) <= (2*r-1)*delta by its
Faddeev identities. Controlling intermediate expansion remains important.

Validation

Run from the sympy-proofs directory:

  .venv-jordan/bin/python sympy-benchmarks/pinv-normalization/experiment.py

Thirteen small cases cover real/complex coefficients, one/two parameters,
ranks 1-3, a complex selected determinant, nonmonomial selected determinants,
rank-preserving zeros of the selected determinant, and an actual rank drop.
Both backends are checked against ambient Faddeev, the sum of squared maximal
minors, all four denominator-cleared Penrose identities, and specialized
SymPy pinv values. Four distinct pivot selections are compared on one family.
These are correctness experiments, not evidence of a performance advantage.

Related literature

1. D. J. Jeffrey, LU Factoring of Non-Invertible Matrices (2010), section 3.4.
   Gives the fraction-free core formula [L (U A.H L)^-1 U].H (permutations
   suppressed), closely related to the core formula used here.
   https://www.uwo.ca/apmaths/faculty/jeffrey/pdfs/David-Jeffrey-LU.pdf

2. G. V. Milovanovic and P. S. Stanimirovic, Rank Factorization and
   Moore-Penrose Inverse, section 3: generalized adjugates and the intrinsic
   sum-of-squared-minors denominator.
   https://www.mi.sanu.ac.rs/~gvm/radovi/blokprim.pdf

3. F. Johansson, On a fast and nearly division-free algorithm for the
   characteristic polynomial (2020): Preparata-Sarwate/Faddeev blocking.
   https://arxiv.org/abs/2011.12573

4. J. Middeke, D. J. Jeffrey, C. Koutschan, Common Factors in Fraction-Free
   Matrix Decompositions (2020): systematic cancellation in fraction-free
   decompositions, relevant to novelty and implementation comparisons.
   https://doi.org/10.1007/s11786-020-00495-9
