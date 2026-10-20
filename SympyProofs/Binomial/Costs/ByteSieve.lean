module

public import SympyProofs.Binomial.Algorithms.ByteSieveGeneratorCorrectness
public import SympyProofs.Python.Cost.BufferIndex
public import SympyProofs.Python.Cost.GeneratorBounds

/-!
# Cost instrumentation for the odd-prime generator

Cost operations are separate from the original generator. The stream delivers
cost events lazily, including the final unsuccessful search on exhaustion.
`ByteSieveRefinement` proves that table construction returns the verified sieve.
`ByteSieveBounds`, `ByteSearchBounds`, and `PrimeStreamBounds` bound its actual
finite event trace, including allocations, searches, and suspension control.
-/

@[expose] public section

universe v

namespace SympyBinomial.ByteSieve

open PythonByteArray
open scoped PythonBytes

variable (B : Type) [PythonByteArray B]

open Python.Cost

/-- One candidate of the instrumented sieve. -/
def markM {m : Type → Type v} [Monad m] [MonadCost m]
    (p : ℕ) (sieve : B) : m B := do
  MonadCost.emit (.control "sieve.next")
  let index ← Index.div p 2
  let flag ← BufferIndex.get sieve index
  MonadCost.emit (.control "sieve.byteTruth")
  if flag ≠ 0 then
    let start ← Index.mul p p >>= fun x => Index.div x 2
    let size ← BufferIndex.length sieve
    let count ← Index.signed .sub (· - ·) size 1
    let count ← Index.signed .sub (· - ·) count start
    let count ← Index.signed .floorDiv Int.fdiv count p
    let count ← Index.signed .add (· + ·) count 1
    let zero ← BufferIndex.literal B 0x00
    let replacement ← BufferIndex.repeatBytes B zero count
    return ← BufferIndex.setSlice sieve start p replacement
  return sieve

/-- Allocate the initial table and clear the nonprime slot for one. -/
def initialM {m : Type → Type v} [Monad m] [MonadCost m] (limit : ℕ) : m B := do
  let one ← BufferIndex.literal B 0x01
  let initial ← BufferIndex.ofBytes (B := B) one
  let count ← Index.add limit 1 >>= fun x => Index.div x 2
  let mut sieve ← BufferIndex.repeatArray initial count
  MonadCost.emit (.control "sieve.truth")
  if 0 < PythonByteArray.size sieve then
    sieve ← BufferIndex.set sieve 0 0
  return sieve

/-- Initialize and mark the byte table before the first generator yield. -/
def sieveM {m : Type → Type v} [Monad m] [MonadCost m] (limit : ℕ) : m B := do
  let mut sieve ← initialM B limit
  let bound ← Index.sqrt limit >>= fun x => Index.add x 1
  for p in [3:bound:2] do
    sieve ← markM B p sieve
  return sieve

/-- Deliver one marked slot and find the next one after resumption. -/
def advanceM {m : Type → Type v} [Monad m] [MonadCost m]
    (yieldPrime : ℕ → m Unit) (sieve : B) (i : ℤ) : m ℤ := do
  let prime ← Index.mul 2 i.toNat >>= fun x => Index.add x 1
  MonadCost.emit (.control "generator.yield")
  yieldPrime prime
  MonadCost.emit (.control "generator.resume")
  let next ← Index.add i.toNat 1
  BufferIndex.find sieve 0x01 next

/-- Resume the search at an index returned by `find`, charging every suspension. -/
def searchM {m : Type → Type v} [Monad m] [MonadCost m]
    [ForIn m Lean.Loop Unit] (yieldPrime : ℕ → m Unit) (sieve : B) (index : ℤ) : m Unit := do
  let mut i := index
  while ← Index.ne i (-1) do
    i ← advanceM B yieldPrime sieve i

/-- The instrumented sieve body, interpreted with ignored or recorded events. -/
def oddPrimesBodyM {m : Type → Type v} [Monad m] [MonadCost m]
    [ForIn m Lean.Loop Unit] (yieldPrime : ℕ → m Unit) (limit : ℕ) : m Unit := do
  let sieve ← sieveM B limit
  MonadCost.emit (.control "sieve.stop")
  let i ← BufferIndex.find sieve 0x01 1
  searchM B yieldPrime sieve i

/-- Execute the instrumented body with cost events ignored. -/
def oddPrimesIgnored (limit : ℕ) : Generator.Computation ℕ Unit :=
  Generator.create fun () => oddPrimesBodyM B Generator.yield limit

/-- Lazy cost stream: events are charged only when the consumer reaches them. -/
def oddPrimesCostStream (limit : ℕ) : Stream ℕ :=
  letI := eventCost (V := ℕ)
  ⟨Generator.create fun () => oddPrimesBodyM B (fun p => Generator.yield (.inr p)) limit⟩

end SympyBinomial.ByteSieve
