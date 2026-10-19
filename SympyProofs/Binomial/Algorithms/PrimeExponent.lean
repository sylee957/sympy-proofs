module

public import SympyProofs.Binomial.Algorithms.ByteSieve
public import SympyProofs.Python.Bitwise
public import SympyProofs.Python.Math

/-!
# Prime-exponent binomial evaluation

This models the nonnegative Python kernel. Its mathematical input contract is
`k ≤ n`. The quotient loop follows Python's `while a`. Its correctness proof uses
`a` as the termination measure: each iteration divides by at least two. The
exponent accumulator is an integer, so subtraction has Python's signed semantics.
The final shift uses natural bitwise arithmetic, without machine-word overflow.

The generic bit operations are imported from `SympyProofs.Python.Bitwise`.
Correctness proofs are in
`SympyProofs.Binomial.Algorithms.PrimeExponentCorrectness`.
-/

@[expose] public section

namespace SympyBinomial.PrimeExponent

open Python.Bitwise
open Python.Math

variable (B : Type) [PythonByteArray B]

/-- Net power of two in the binomial, with signed intermediate subtraction. -/
def valuation (n k : ℕ) : ℤ :=
  (bitCount k : ℤ) + bitCount (n - k) - bitCount n

/-- Python's balanced product, with a configurable positive leaf size defaulting to 32. -/
def balancedFactors (factors : Array ℕ) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) : ℕ := Id.run do
  let rec «rec» (lo hi : ℕ) : ℕ := Id.run do
    have : 0 < leaf := hleaf
    if hi - lo ≤ leaf then
      return prod factors[lo:hi].toArray
    let mid := (lo + hi) / 2
    return «rec» lo mid * «rec» mid hi
  termination_by hi - lo
  decreasing_by all_goals omega
  return «rec» 0 factors.size

/-- The prime-exponent kernel; the correctness domain is `k ≤ n`. -/
def primeExponents (n k : ℕ) : ℕ := Id.run do
  if k = 0 then
    return 1
  let mut factors : Array ℕ := #[]
  for p in ByteSieve.oddPrimes B n do
    let mut a := n
    let mut b := k
    let mut c := n - k
    let mut e : ℤ := 0
    while a ≠ 0 do
      a := a / p
      b := b / p
      c := c / p
      e := e + (a : ℤ) - b - c
    if e ≠ 0 then
      factors := factors.push (p ^ e.toNat)
  return balancedFactors factors <<< (valuation n k).toNat

end SympyBinomial.PrimeExponent
