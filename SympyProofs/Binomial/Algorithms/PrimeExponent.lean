module

public import SympyProofs.Binomial.Algorithms.ByteSieveGenerator
public import SympyProofs.Python.Int
public import SympyProofs.Python.Math

/-!
# Prime-exponent binomial evaluation

This models the nonnegative Python kernel. Its mathematical input contract is
`0 ≤ k ≤ n`. The quotient loop follows Python's `while a`. Its correctness proof uses
`a` as the termination measure: each iteration divides by at least two. The
exponent accumulator is an integer, so subtraction has Python's signed semantics.
All arithmetic values use the abstract `PythonInt` carrier, without machine-word overflow.
Odd primes are consumed lazily from the stackless generator, as in Python.
The sieve and array bounds retain natural indices; conversion to the integer
carrier happens when each generated prime enters the arithmetic kernel.
Correctness proofs are in
`SympyProofs.Binomial.Algorithms.PrimeExponentCorrectness`.
-/

@[expose] public section


namespace SympyBinomial.PrimeExponent

open PythonInt
open Python.Math

variable (I B : Type) [PythonInt I] [PythonByteArray B]

/-- Net power of two in the binomial, with signed intermediate subtraction. -/
def valuation (n k : Value I) : I :=
  k.bitCount + (n - k).bitCount - n.bitCount

/-- Python's balanced product, with a configurable positive leaf size defaulting to 32. -/
def balancedFactors (factors : Array I) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) : I := Id.run do
  let rec «rec» (lo hi : ℕ) : I := Id.run do
    have : 0 < leaf := hleaf
    if hi - lo ≤ leaf then
      return prod factors[lo:hi].toArray
    let mid := (lo + hi) / 2
    return «rec» lo mid * «rec» mid hi
  termination_by hi - lo
  decreasing_by all_goals omega
  return «rec» 0 factors.size

/-- The prime-exponent kernel; its correctness domain is `0 ≤ k ≤ n`. -/
def primeExponents (n k : Value I) : I := Id.run do
  if k == 0 then
    return 1
  let mut factors : Array I := #[]
  for prime in ByteSieve.oddPrimesGenerator B n.toNat do
    let p : Value I := (prime : I)
    let mut a := n
    let mut b := k
    let mut c := n - k
    let mut e : Value I := 0
    while a != 0 do
      a := a / p
      b := b / p
      c := c / p
      e := e + (a - b - c)
    if e != 0 then
      factors := factors.push (p ^ e)
  return balancedFactors I factors <<< valuation I n k

end SympyBinomial.PrimeExponent
