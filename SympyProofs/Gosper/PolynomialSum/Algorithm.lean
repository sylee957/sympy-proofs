module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Executable polynomial antidifference

`antidifference` takes a polynomial and returns its antidifference with constant
coefficient zero. Internally, `antidifferenceCoefficients` processes coefficients
in increasing degree order, and the output vector is packaged as a polynomial.
The coefficient interface also accepts explicit size bounds.

Each monomial primitive is generated in place from the preceding row by rational
scaling. The initial primitive is `X`; subsequent rows have their linear
coefficient chosen to make their value at one zero. Contributions to the output
are accumulated in the same loop. The recurrence uses no Bernoulli or binomial
calls, coefficient zero tests, or parameter-dependent division. The polynomial
interface obtains its size bound from the input's `natDegree`.

For an input of length `N`, it takes `O(N²)` arithmetic operations and `O(N)`
storage, counting coefficient accesses as constant time and excluding the bit
complexity of arithmetic. Correctness is proved in `PolynomialSum.Correctness`,
with `antidifference_sound` stating the difference identity and normalization.
-/

@[expose] public section

namespace Gosper.PolynomialSum

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Executable summation on dense coefficients, listed from constant term upward.
An input vector of length `N` produces one of length `N + 1`; trailing zeros
are allowed. The imperative recurrence updates one rational row in descending
order and accumulates its contribution, with no zero tests on the coefficient ring. -/
def antidifferenceCoefficients {N : ℕ} (a : Fin N → R) : Vector R (N + 1) := Id.run do
  let mut row := Vector.replicate (N + 1) (0 : ℚ)
  let mut q := Vector.replicate (N + 1) (0 : R)
  for hn : n in [:N] do
    have hn : n < N := hn.upper
    let coefficient := a ⟨n, hn⟩
    let mut total := (0 : ℚ)
    -- Descend so each old coefficient is read before it is overwritten.
    for hj : j in [:n] do
      have hj : j < n := hj.upper
      let k := n + 1 - j
      let c := (n : ℚ) / k * row[k - 1]'(by omega)
      row := row.set k c (by omega)
      total := total + c
      q := q.set k (q[k] + coefficient * algebraMap ℚ R c) (by omega)
    -- Fix the linear coefficient using the value at one.
    let c := if n = 0 then 1 else -total
    row := row.set 1 c (by omega)
    q := q.set 1 (q[1] + coefficient * algebraMap ℚ R c) (by omega)
  return q

/-- Compute the normalized antidifference directly from a polynomial.
The degree bound and coefficient extraction are handled internally. -/
def antidifference [DecidableEq R] (p : R[X]) : R[X] :=
  let q := antidifferenceCoefficients (N := p.natDegree + 1) (fun n => p.coeff n.val)
  Polynomial.ofFn (p.natDegree + 2) (fun k => q[k.val])

end Gosper.PolynomialSum
