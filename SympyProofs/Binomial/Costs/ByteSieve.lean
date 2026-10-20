module

public import SympyProofs.Binomial.Algorithms.ByteSieveGeneratorCorrectness
public import SympyProofs.Python.Cost.BufferIndex
public import SympyProofs.Python.Cost.GeneratorBounds
public import SympyProofs.Python.Cost.Instrumentation.Monadic
public meta import SympyProofs.Binomial.Costs.ByteSieveFragments

/-!
# Cost instrumentation for the odd-prime generator

`oddPrimesGenerated` is generated from the original generator's elaborated body.
The stream delivers cost events lazily, including the final unsuccessful search
on exhaustion. The phase definitions are extracted from that generated body:
`oddPrimesBodyM_eq` proves exact computational equality to the generated body,
so the phase bounds apply to the automatically instrumented source.
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

derive_costed_generator oddPrimesGenerator as oddPrimesGenerated

-- Initialization, marking, and search are selected from the generated computation.
extract_sieve_fragments oddPrimesGenerated

/-- Generated from the original body; its caller supplies the suspension operation. -/
def oddPrimesBodyM {m : Type → Type v} [Monad m] [MonadCost m]
    [ForIn m Lean.Loop Unit] (yieldPrime : ℕ → m Unit) (limit : ℕ) : m Unit :=
  oddPrimesGenerated B limit yieldPrime

private theorem bind_ite' {m : Type → Type v} [Monad m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- The extracted prefix consists of initialization and the extracted marking updates. -/
theorem sieveM_eq {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadCost m]
    (limit : ℕ) :
    sieveM (m := m) B limit = (do
      let bytes ← initialM B limit
      let bound ← Index.sqrt limit >>= fun x => Index.add x 1
      ForIn.forIn ([3:bound:2] : Std.Legacy.Range) bytes
        (fun p bytes => ForInStep.yield <$> markM B p bytes)) := by
  simp only [sieveM, initialM, markM, Index.sqrt, Index.add, Index.binary, perform,
    LawfulMonad.bind_assoc, LawfulMonad.pure_bind, _root_.bind_pure,
    bind_ite', decide_eq_true_eq, map_eq_pure_bind]

/-- Exact computational equality to the phases used by the lazy trace and resource proofs. -/
theorem oddPrimesBodyM_eq {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadCost m]
    [ForIn m Lean.Loop Unit] (yieldPrime : ℕ → m Unit) (limit : ℕ) :
    oddPrimesBodyM B yieldPrime limit = (do
      let sieve ← sieveM B limit
      MonadCost.emit (.control "sieve.stop")
      let i ← BufferIndex.find sieve 0x01 1
      searchM B yieldPrime sieve i) := by
  simp only [oddPrimesBodyM, oddPrimesGenerated, sieveM, searchM, BufferIndex.find,
    perform, LawfulMonad.bind_assoc, LawfulMonad.pure_bind, bind_ite', decide_eq_true_eq]

/-- Lazy cost stream: events are charged only when the consumer reaches them. -/
def oddPrimesCostStream (limit : ℕ) : Stream ℕ :=
  letI := eventCost (V := ℕ)
  ⟨Generator.create fun () => oddPrimesBodyM B (fun p => Generator.yield (.inr p)) limit⟩

section
open Generator
local instance : MonadCost (Generator.Computation (Event ⊕ ℕ)) := eventCost

/-- One resume of the extracted search loop, shared by resource and erasure proofs. -/
theorem searchM_step (bytes : B) (i : ℤ) :
    (searchM (m := Generator.Computation (Event ⊕ ℕ)) B (fun p => Generator.yield (.inr p)) bytes i).step =
      .skip (do
        let test ← Index.ne i (-1)
        if test then
          let next ← advanceM B (fun p => Generator.yield (.inr p)) bytes i
          searchM B (fun p => Generator.yield (.inr p)) bytes next
        else pure ()) := by
  by_cases h : i = -1 <;>
    simp [searchM,ForIn.forIn,Computation.step,Index.ne,perform,MonadCost.emit,Bind.bind,Pure.pure,
      Generator.bind,Generator.yield,h,advanceM]

end

end SympyBinomial.ByteSieve
