module

public import SympyProofs.Python.ByteArray

/-!
# Byte-array model of the odd-only Eratosthenes sieve

Slot `i` represents `2 * i + 1`. The carrier `B` is abstract: the algorithm uses only
the operations and laws in `PythonByteArray B`, with no access to storage.
The bytearray operations and their slice/search contracts are imported from
`SympyProofs.Python.ByteArray`. Correctness proofs are in
`SympyProofs.Binomial.Algorithms.ByteSieveCorrectness`.
-/

@[expose] public section

namespace SympyBinomial.ByteSieve

open PythonByteArray
open scoped PythonBytes

variable (B : Type) [PythonByteArray B]

/-- Model `list(odd_primes(limit))`: collect the generator's values by successive `find` calls. -/
def oddPrimes (limit : ℕ) : Array ℕ := Id.run do
  let mut sieve : Value B := (bytearray (b[0x01]) : B) * ((limit + 1) / 2)
  if 0 < sieve.size then
    sieve := sieve.set! 0 0
  for hp : p in [3:limit.sqrt + 1:2] do
    if sieve[p / 2]! ≠ 0 then
      let start := p * p / 2
      let count := (sieve.len - 1 - (start : ℤ)).fdiv p + 1
      have hp_pos : 0 < p := by have h : 3 ≤ p := hp.lower; omega
      sieve := sieve.setSlice start p ((b[0x00] : Bytes B) * count)
        hp_pos (by simpa [count] using size_singleton_mul_sliceCount sieve 0 start p hp_pos)
  let mut primes := #[]
  let mut i := sieve.find 0x01 1
  while i ≠ -1 do
    primes := primes.push (2 * i.toNat + 1)
    i := sieve.find 0x01 (i.toNat + 1)
  return primes

end SympyBinomial.ByteSieve
