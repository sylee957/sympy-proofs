module

public import SympyProofs.Binomial.Algorithms.PrimeExponentCorrectness
public import SympyProofs.Python.Cost.Models
public import SympyProofs.Binomial.Costs.ByteSieve
public import SympyProofs.Python.Cost.Sequence
public import SympyProofs.Python.Cost.Instrumentation.Monadic
public meta import SympyProofs.Binomial.Costs.PrimeExponentFragments

/-!
# Cost interpretation of prime-exponent evaluation

`valuationM` is generated from the elaborated body of `valuation`; there is no
second arithmetic formula to maintain. The original algorithm stays unchanged.
`valuationM_id` proves value equivalence, and
`valuation_trace` checks the exact evaluation order and operation events.
It makes six primitive calls, of which three are bit counts. This is a call count,
not constant bit complexity: the operands' widths remain in the events.
The complete kernel is instrumented by `primeExponentsM`, including the lazy sieve,
quotient loops, powers, list allocation, balanced multiplication and final shift.
The complete body and the original well-founded product recursion are translated
from elaborated source. Quotient and consumer proof fragments are then extracted
from the complete source and generated kernels, without separate loop definitions.
The sieve stream is likewise generated. Unfolding equations identify the generated computations with
the phases used by the compositional resource proofs; they preserve effects,
not just return values.
`PrimeExponentErasure` proves equivalence of the complete costed program to the
original imperative kernel, for every charging policy and initial counter.
The complete executed counter is bounded in `FullAsymptotics`, using contracts for
the producer, consumer, and arithmetic phases. Valuation-specific asymptotics
are in `PrimeExponentAsymptotics`.
-/

@[expose] public section

universe v

namespace SympyBinomial.PrimeExponent

open PythonInt Python.Cost

variable (I : Type) [PythonInt I]

derive_costed valuation as valuationInstrumented

/-- Interpret automatically generated instrumentation of the original formula. -/
def valuationM {m : Type → Type v} [Monad m] [MonadCost m]
    (n k : Value I) : m I :=
  (valuationInstrumented I n k).run

/-- Erasing the instrumentation recovers the algorithm's formula. -/
theorem valuationM_id (n k : Value I) :
    valuationM (m := Id) I n k = valuation I n k :=
  (valuationInstrumented I n k).run_id

/-- The event sequence computed by the automatically instrumented formula. -/
def valuationEvents (n k : Value I) : List Event :=
  (valuationInstrumented I n k).program.events

/-- The trace records all six calls, including reused operands and intermediate results. -/
theorem valuation_trace (n k : Value I) :
    TraceT.run (valuationM (m := TraceT Id) I n k) =
      (valuation I n k, valuationEvents I n k) :=
  (valuationInstrumented I n k).run_trace

/-- Every charging policy changes only cost, not the computed valuation. -/
theorem valuation_run (n k : Value I) (model : Model) (initial : ℕ := 0) :
    CostT.run (valuationM (m := CostT Id) I n k) model initial =
      (valuation I n k, initial + charge model (valuationEvents I n k)) :=
  (valuationInstrumented I n k).run_cost model initial

/-- This exact count is independent of the integer magnitudes. -/
theorem valuation_operations (n k : Value I) :
    CostT.run (valuationM (m := CostT Id) I n k) Models.operations =
      (valuation I n k, 6) := by
  rw [valuation_run I n k Models.operations 0]
  simp [valuationEvents, valuationInstrumented, Instrumentation.Checked.bind,
    Instrumentation.Checked.primitive, Instrumentation.Checked.pure,
    Instrumentation.Checked.pyBitCount, Instrumentation.Checked.pySub,
    Instrumentation.Checked.pyAdd, Instrumentation.Program.events, Instrumentation.Program.value]

theorem valuation_bitCount_calls (n k : Value I) :
    charge (Models.integerCalls .bitCount) (valuationEvents I n k) = 3 := by
  simp [charge, valuationEvents, valuationInstrumented, Instrumentation.Checked.bind,
    Instrumentation.Checked.primitive, Instrumentation.Checked.pure,
    Instrumentation.Checked.pyBitCount, Instrumentation.Checked.pySub,
    Instrumentation.Checked.pyAdd, Instrumentation.Program.events, Instrumentation.Program.value,
    Models.integerCalls]

/-- Costed execution retains the established arithmetic correctness theorem. -/
theorem valuation_run_eq_factorization (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) (model : Model) :
    toInt (CostT.run (valuationM (m := CostT Id) I n k) model).1 =
      (((toNat n).choose (toNat k)).factorization 2 : ℤ) := by
  rw [valuation_run I n k model 0]
  exact valuation_eq_factorization I n k hk0 hk

derive_costed_monadic balancedFactors.rec._unary as balancedFactorsUnaryM
  using [] streams []

/-- The original well-founded measure and termination proofs are retained. -/
def balancedFactorsM.rec {m : Type → Type v} [Monad m] [MonadCost m]
    (factors : Array I) (leaf : ℕ) (hleaf : 0 < leaf) (lo hi : ℕ) : m I :=
  balancedFactorsUnaryM I factors leaf hleaf ⟨lo, hi⟩

/-- Unfolding equation used to compose resource contracts for the generated recursion. -/
theorem balancedFactorsM_rec_eq {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadCost m]
    (factors : Array I) (leaf : ℕ) (hleaf : 0 < leaf) (lo hi : ℕ) :
    balancedFactorsM.rec (m := m) I factors leaf hleaf lo hi = (do
      let _ ← Index.sub hi lo
      let _ ← Index.le (hi - lo) leaf
      if hi - lo ≤ leaf then
        let xs ← Sequence.slice factors lo hi
        Sequence.prod xs
      else
        let _ ← Index.add lo hi
        let _ ← Index.div (lo + hi) 2
        let a ← balancedFactorsM.rec I factors leaf hleaf lo ((lo + hi) / 2)
        let b ← balancedFactorsM.rec I factors leaf hleaf ((lo + hi) / 2) hi
        Python.Cost.Int.mul a b) := by
  conv_lhs =>
    unfold balancedFactorsM.rec balancedFactorsUnaryM
    rw [WellFounded.Nat.fix_eq]
  simp only [Index.sub, Index.add, Index.div, Index.binary, Index.le,
    Sequence.slice, Python.Cost.Int.mul, Python.Cost.Int.binary,
    balancedFactorsM.rec, balancedFactorsUnaryM,
    perform, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  split <;> rfl

derive_costed_monadic balancedFactors.rec as balancedFactorsRecEntry
  using [balancedFactors.rec._unary, balancedFactorsUnaryM] streams []

derive_costed_monadic balancedFactors as balancedFactorsGenerated
  using [balancedFactors.rec, balancedFactorsRecEntry] streams []

/-- Compatibility interface to the generated product tree. -/
def balancedFactorsM {m : Type → Type v} [Monad m] [MonadCost m]
    (factors : Array I) (leaf : ℕ := 32) (hleaf : 0 < leaf := by omega) : m I :=
  balancedFactorsGenerated I factors leaf hleaf

private theorem balancedFactorsM_rec_id (factors : Array I) (leaf : ℕ)
    (hleaf : 0 < leaf) (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ factors.size) :
    balancedFactorsM.rec (m := Id) I factors leaf hleaf lo hi =
      balancedFactors.rec I factors leaf hleaf lo hi := by
  rw [balancedFactorsM_rec_eq, balancedFactors.rec]
  by_cases h : hi - lo ≤ leaf
  · simp only [h, ↓reduceIte]
    change Python.Math.prod (factors.extract lo hi) = Python.Math.prod (factors[lo:hi].toArray)
    congr 1
    apply Array.toList_inj.mp
    simp [Subarray.toList_eq, Subarray.toList_toArray,
      Nat.min_eq_left hhi, Nat.min_eq_left hlo]
  · simp only [h, ↓reduceIte]
    change (Id.run (balancedFactorsM.rec (m := Id) I factors leaf hleaf lo ((lo + hi) / 2))) *
      (Id.run (balancedFactorsM.rec (m := Id) I factors leaf hleaf ((lo + hi) / 2) hi)) = _
    rw [balancedFactorsM_rec_id factors leaf hleaf lo ((lo + hi) / 2) (by omega) (by omega),
      balancedFactorsM_rec_id factors leaf hleaf ((lo + hi) / 2) hi (by omega) hhi]
    rfl
termination_by hi - lo
decreasing_by all_goals omega

theorem balancedFactorsM_id (factors : Array I) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) :
    balancedFactorsM (m := Id) I factors leaf hleaf = balancedFactors I factors leaf hleaf := by
  exact balancedFactorsM_rec_id I factors leaf hleaf 0 factors.size (by omega) (by omega)

derive_costed_monadic primeExponents as primeExponentsM
  using [balancedFactors, balancedFactorsGenerated]
  streams [ByteSieve.oddPrimesGenerator, ByteSieve.oddPrimesCostStream]

-- Both proof views are selected from their respective complete kernels.
extract_prime_fragments primeExponents
extract_prime_fragments primeExponentsM

private theorem bind_ite' {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c]
 (a b : m α) (f : α → m β) : (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl
/-- The extracted transition is exactly the transition used by the extracted loop. -/
theorem quotientExponentM_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadCost m]
    (n k p : I) :
    quotientExponentM (m := m) I n k p = (do
      let c ← Python.Cost.Int.sub n k
      let state ← Lean.Loop.forIn ⟨⟩ (n, k, c, 0) (fun _ => quotientStepM (m := m) I p)
      pure state.2.2.2) := rfl

/-- The consumer's source fragment returns the optional factor after its quotient loop. -/
theorem factorCode_eq (n k : I) (p : ℕ) (factors : Array I) :
    factorCode I n k p factors =
      let e := quotientCode I n k (p : I)
      if e != 0 then factors.push ((p : I) ^ e) else factors := rfl

/-- Recompose the generated consumer from its extracted loop and final conditional. -/
theorem primeFactorM_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadCost m]
    (n k : I) (p : ℕ) (factors : Array I) :
    primeFactorM (m := m) I n k p factors = (do
      MonadCost.emit (.control "for.next")
      let e ← quotientExponentM I n k (p : I)
      let test ← Python.Cost.Int.eq e 0
      if !test then
        let power ← Python.Cost.Int.pow (p : I) e
        Sequence.append factors power
      else pure factors) := by
  simp only [primeFactorM, quotientExponentM, Python.Cost.Int.eq, Python.Cost.Int.pow,
    Python.Cost.Int.binary, perform, LawfulMonad.bind_assoc, LawfulMonad.pure_bind,
    _root_.bind_pure]
  rfl

/-- A compositional unfolding of the generated full program, with the same effects. -/
theorem primeExponentsM_eq {m : Type → Type} [Monad m] [LawfulMonad m] [MonadCost m]
    (B : Type) [PythonByteArray B] (n k : I) :
    primeExponentsM (m := m) I B n k = (do
      if ← Python.Cost.Int.eq k 0 then return 1
      let factors ← Sequence.empty
      let factors ← ForIn.forIn (SympyBinomial.ByteSieve.oddPrimesCostStream B (toNat n)) factors
        (fun p factors => ForInStep.yield <$> primeFactorM (m := m) I n k p factors)
      MonadCost.emit (.control "for.stop")
      let value ← balancedFactorsM I factors
      let shift ← valuationM I n k
      Python.Cost.Int.shiftLeft value shift) := by
  simp only [primeExponentsM, primeFactorM,
    map_eq_pure_bind, LawfulMonad.bind_assoc, LawfulMonad.pure_bind, bind_ite', balancedFactorsM, valuationM, valuationInstrumented,
    Instrumentation.Checked.run, Instrumentation.Checked.bind,
    Instrumentation.Checked.pure, Instrumentation.Checked.primitive,
    Instrumentation.Checked.pyBitCount, Instrumentation.Checked.pySub,
    Instrumentation.Checked.pyAdd, Instrumentation.Program.run]
  rfl

/-- The complete execution takes only its initial equality test when `k = 0`.
In particular, it does not construct or resume the sieve. -/
theorem primeExponentsM_zero_run (B : Type) [PythonByteArray B] (n : I) (initial : ℕ) :
    CostT.run (primeExponentsM (m := CostT Id) I B n 0) Models.schoolbook initial =
      (1, initial + 2) := by
  simp [primeExponentsM_eq, Python.Cost.Int.eq, CostT.run, perform, MonadCost.emit]
  rfl

end SympyBinomial.PrimeExponent
