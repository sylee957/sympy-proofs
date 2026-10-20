/-
Run after `lake build SympyProofs.Binomial`:
  lake env lean scripts/check_python_costs.lean

Generated instrumentation of ordinary imperative bodies, suspension, operation
coverage, custom-instance rejection, and the PythonInt buffer boundary.
-/
import SympyProofs.Binomial.Costs
import SympyProofs.Python.Cost.ByteArray
import SympyProofs.Python.Cost.SequenceWorstCase
import SympyProofs.Python.Int.Native
import SympyProofs.Python.ByteArray.Native
import SympyProofs.Binomial.Costs.ByteSieveFragments
import SympyProofs.Binomial.Costs.PrimeExponentFragments

open PythonInt Python.Cost
open scoped PythonBytes

section Abstract
variable (I : Type) [PythonInt I]

def updates (input : I) : I := Id.run do
  let mut x := input
  x := x + 1
  x := x * x
  return x

derive_costed_monadic updates as updatesM using [] streams []

example (x : I) : Id.run (updatesM I x (m := Id)) = (x + 1) * (x + 1) := rfl
example (x : I) : CostT.run (updatesM I x (m := CostT Id)) Models.operations =
    ((x + 1) * (x + 1), 2) := rfl

def reuse (input : I) : I := Id.run do
  let square := input * input
  let extra := square + 1
  return extra - square

derive_costed_monadic reuse as reuseM using [] streams []
example (x : I) : CostT.run (reuseM I x (m := CostT Id)) Models.operations =
    (x * x + 1 - x * x, 3) := rfl

def yielding (input : I) : Generator.Computation I I := Generator.create fun () => do
  let y := input + 1
  Generator.yield y
  return y * y

derive_costed_generator yielding as yieldingBodyM

-- Before suspension: one addition and the yield event. After resumption:
-- the resume event and one multiplication. No producer work is charged early.
example (x : I) :
    CostT.run (yieldingBodyM I x (m := CostT (Generator.Computation I))
      (fun y => liftM (Generator.yield y))) Models.operations =
    Generator.Computation.suspended (x + 1)
      (fun () => .done ((x + 1) * (x + 1), 4)) := rfl

def branching (input : I) : I := if input < 0 then -input else input * input + 1
derive_costed_monadic branching as branchingM using [] streams []

def countdown (input : I) : I := Id.run do
  let mut x := input
  while x != 0 do
    x := x - 1
  return x

derive_costed_monadic countdown as countdownM using [] streams []
end Abstract

abbrev I := PythonInt.Native
abbrev B := PythonByteArray.Native
abbrev S := PythonBytes.Native

def runInt (program : CostT Id I) (model : Model) : ℤ × ℕ :=
  let (result, total) := Id.run (CostT.run program model)
  (toInt result, total)

#guard runInt (updatesM I 4) Models.operations == (25, 2)
#guard runInt (reuseM I 9) Models.operations == (1, 3)
#guard runInt (branchingM I (-4)) Models.operations == (4, 2)
#guard runInt (branchingM I 4) Models.operations == (17, 3)
#guard runInt (countdownM I 4) Models.operations == (0, 9)
#guard runInt (countdownM I 0) Models.operations == (0, 1)

-- Even extensionally identical custom sequencing instances need a contract.
@[instance_reducible] def otherPure : Pure Id := ⟨fun a => a⟩
def changedPure (n : ℕ) : ℕ := Id.run (@Pure.pure Id otherPure ℕ n)
/--
error: instrumentation: resolved call @pure does not match contract @Instrumentation.Checked.idPure (including its instances)
-/
#guard_msgs in
derive_costed_monadic changedPure as changedPureM using [] streams []

@[instance_reducible] def otherLoop : ForIn Id Lean.Loop Unit := inferInstance
def changedLoop (n : ℕ) : ℕ :=
  @ForIn.forIn Id Lean.Loop Unit otherLoop ℕ ⟨⟩ n (fun _ a => pure (.done a))
/-- error: instrumentation: unsupported iterator instance -/
#guard_msgs in
derive_costed_monadic changedLoop as changedLoopM using [] streams []

-- Search preserves signed -1 and charges only the inspected suffix in this model.
def bytes : B := bytearray (b[0x00, 0x01, 0x00, 0x01])
def one : S := b[0x01]
def noMatch : S := b[0x02]

#guard runInt (ByteArray.find bytes one (1 : I) (by decide) : CostT Id I)
    Models.byteReads == (1, 1)
#guard runInt (ByteArray.find bytes one (2 : I) (by decide) : CostT Id I)
    Models.byteReads == (3, 2)
#guard runInt (ByteArray.find bytes noMatch (1 : I) (by decide) : CostT Id I)
    Models.byteReads == (-1, 3)
#guard runInt (ByteArray.find bytes one (8 : I) (by decide) : CostT Id I)
    Models.byteReads == (-1, 0)

#guard PythonBytes.size ((CostT.run (Bytes.repeat one (-4 : I) : CostT Id S)
    Models.createdBytes).1) == 0
#guard (CostT.run (Bytes.repeat one (7 : I) : CostT Id S) Models.createdBytes).2 == 7
#guard (CostT.run (Python.Cost.ByteArray.set bytes (2 : I) (255 : I) : CostT Id B)
    Models.createdBytes).2 == 0
#guard PythonByteArray.IntAPI.get
    ((CostT.run (Python.Cost.ByteArray.set bytes (2 : I) (255 : I) : CostT Id B) Models.byteWrites).1)
    (2 : I) == 255

-- A replacement is read/written separately from its earlier allocation.
def replacement : S := b[0x00, 0x00]
def sliceProgram : CostT Id B :=
  ByteArray.setSlice bytes (1 : I) (2 : I) replacement (by decide) (by decide)
#guard (CostT.run sliceProgram Models.byteWrites).2 == 2
#guard (CostT.run sliceProgram Models.createdBytes).2 == 0
#guard PythonByteArray.toArray (CostT.run sliceProgram Models.operations).1 == #[0, 0, 0, 0]

-- Repricing the exact trace agrees with direct accumulation, including initial cost.
open SympyBinomial.PrimeExponent in
#guard (CostT.run (valuationM (m := CostT Id) I 1000 400) Models.schoolbook 17).2 ==
  17 + charge Models.schoolbook (TraceT.run (valuationM (m := TraceT Id) I 1000 400)).2

#print axioms SympyBinomial.PrimeExponent.valuation_run_eq_factorization

-- The asymptotic results concern these actual executed counters.
#guard runInt (Sequence.prod (#[] : Array I)) Models.schoolbook == (1, 1)
#guard runInt (Sequence.prod (#[2] : Array I)) Models.schoolbook == (2, 7)
#guard runInt (Sequence.prod (#[2, 2, 2, 2] : Array I)) Models.operations == (16, 9)
#guard runInt (Sequence.prod (#[2, 2, 2, 2] : Array I)) Models.schoolbook == (16, 43)

#print axioms SympyBinomial.PrimeExponent.valuation_isTheta_log2
#print axioms Python.Cost.Sequence.prod_schoolbook_isBigO
#print axioms Python.Cost.Sequence.prod_twos_isTheta

-- A helper mapping cannot substitute a value-equivalent implementation that omits events.
def increment (n : ℕ) := n + 1
derive_costed_monadic increment as incrementM using [] streams []
def callsIncrement (n : ℕ) := increment n

def unchargedIncrement (n : ℕ) {m : Type → Type u} [Monad m] [MonadCost m] : m ℕ := pure (n + 1)
/-- error: instrumentation: helper adapter does not match the generated computation -/
#guard_msgs in
derive_costed_monadic callsIncrement as badIncrementM
  using [increment, unchargedIncrement] streams []

derive_costed_monadic callsIncrement as callsIncrementM
  using [increment, incrementM] streams []
example (n : ℕ) : CostT.run (callsIncrementM n (m := CostT Id)) Models.operations = (n+1,1) := rfl

-- The whole generated kernel reprices its actual lazy trace, including a nonzero initial counter.
open SympyBinomial.PrimeExponent in
#guard (CostT.run (primeExponentsM (m := CostT Id) I B 100 50) Models.schoolbook 17).2 ==
  17 + charge Models.schoolbook (TraceT.run (primeExponentsM (m := TraceT Id) I B 100 50)).2

#print axioms SympyBinomial.PrimeExponent.primeExponentsM_eq
#print axioms SympyBinomial.ByteSieve.oddPrimesBodyM_eq
#print axioms SympyBinomial.PrimeExponent.balancedFactorsM_rec_eq
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_run_eq_choose
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_schoolbook_le

-- Proof fragments must come from a registered generated producer.
/-- error: fragment extraction requires a registered generated producer -/
#guard_msgs in
extract_sieve_fragments SympyBinomial.ByteSieve.oddPrimesBodyM

-- Extracting an update cannot erase a break, nor leave a hidden captured input.
open Lean Meta Elab in
/-- error: fragment extraction: expected a yielding return -/
#guard_msgs in
run_elab do
  let stx ← `((pure (ForInStep.done (1 : ℕ)) : Id (ForInStep ℕ)))
  let body ← Term.elabTerm stx none
  discard <| Python.Cost.Instrumentation.Fragments.yieldingValue
    { monad := mkConst ``Id [0] } body

open Lean Meta Elab in
/-- error: fragment extraction: rejectedCapture captures an undeclared parameter -/
#guard_msgs in
run_elab do
  withLocalDeclD `hidden (mkConst ``Nat) fun hidden =>
    Python.Cost.Instrumentation.Fragments.define `rejectedCapture [] #[] hidden

#print axioms SympyBinomial.ByteSieve.sieveM_eq

-- Being value-equivalent to the kernel does not authorize an extraction target.
def copiedKernel (I B : Type) [PythonInt I] [PythonByteArray B] (n k : Value I)
    {m : Type → Type u} [Monad m] [MonadCost m] : m I :=
  SympyBinomial.PrimeExponent.primeExponentsM I B n k

/-- error: fragment extraction requires a registered generated kernel -/
#guard_msgs in
extract_prime_fragments copiedKernel

#print axioms SympyBinomial.PrimeExponent.quotientExponentM_eq
#print axioms SympyBinomial.PrimeExponent.factorCode_eq
#print axioms SympyBinomial.PrimeExponent.primeFactorM_eq
