import SympyProofs.Python.Cost.Instrumentation.Derive
import SympyProofs.Python.Int.Native
import SympyProofs.Python.Cost.Models
import SympyProofs.Binomial.Costs.PrimeExponent

/-! Run with `lake env lean scripts/check_instrumentation.lean`.
These checks exercise source elaboration, evaluation order, sharing, early
termination, composition, rejection and the exported certificates.
-/

open Lean Elab Term
open Python.Cost Python.Cost.Instrumentation
namespace InstrumentationTests

macro "double% " x:term : term => `(($x) + ($x))
elab "successor% " x:term : term => do
  elabTerm (← `(($x) + 1)) none

def notationExample (n : ℕ) := double% (successor% n)
derive_costed notationExample as notationCost

-- The macro duplicates its argument: both additions by one must be counted.
example : (notationCost 4).program.events =
    [.integer ⟨.add, [4, 1], 5⟩, .integer ⟨.add, [4, 1], 5⟩,
      .integer ⟨.add, [5, 5], 10⟩] := rfl

def shared (n k : ℕ) := Id.run do
  let a := n * k
  return a + a
derive_costed shared as sharedCost

example : (sharedCost 4 5).program.events =
    [.integer ⟨.mul, [4, 5], 20⟩, .integer ⟨.add, [20, 20], 40⟩] := rfl

def imperative (n k : ℕ) := Id.run do
  let mut a := n + k
  if a < n then
    a := a * 2
  else
    a := a - 1
  return a
derive_costed imperative as imperativeCost

example : (imperativeCost 2 3).program.events =
    [.integer ⟨.add, [2, 3], 5⟩, .integer ⟨.lt, [5, 2], 0⟩,
      .integer ⟨.sub, [5, 1], 4⟩] := rfl

-- Truncated Nat subtraction must also be truncated in the reported result.
example : (imperativeCost 0 0).program.events =
    [.integer ⟨.add, [0, 0], 0⟩, .integer ⟨.lt, [0, 0], 0⟩,
      .integer ⟨.sub, [0, 1], 0⟩] := rfl

def sequenced (n k : ℕ) := Id.run do
  let a ← pure (n + k)
  return a * a
derive_costed sequenced as sequencedCost

example : (sequencedCost 2 3).program.events =
    [.integer ⟨.add, [2, 3], 5⟩, .integer ⟨.mul, [5, 5], 25⟩] := rfl

def helper (n : ℕ) := n * n
derive_costed helper as helperCost
def composed (n : ℕ) := helper (n + 1) + helper n
derive_costed composed as composedCost

example : (composedCost 3).program.events =
    [.integer ⟨.add, [3, 1], 4⟩, .integer ⟨.mul, [4, 4], 16⟩,
      .integer ⟨.mul, [3, 3], 9⟩, .integer ⟨.add, [16, 9], 25⟩] := rfl

def untilZero (xs : List ℕ) := Id.run do
  let mut acc := 0
  for x in xs do
    if x == 0 then break
    acc := acc + x * x
  return acc
derive_costed untilZero as untilZeroCost

example : (untilZeroCost [2, 3, 0, 100]).program.events =
    [.control "for.next", .integer ⟨.eq, [2, 0], 0⟩,
      .integer ⟨.mul, [2, 2], 4⟩, .integer ⟨.add, [0, 4], 4⟩,
      .control "for.next", .integer ⟨.eq, [3, 0], 0⟩,
      .integer ⟨.mul, [3, 3], 9⟩, .integer ⟨.add, [4, 9], 13⟩,
      .control "for.next", .integer ⟨.eq, [0, 0], 1⟩] := rfl

example : (untilZeroCost []).program.events = [] := rfl

example (xs : List ℕ) (model : Model) (initial : ℕ) :
    CostT.run ((untilZeroCost xs).run (m := CostT Id)) model initial =
      (untilZero xs, initial +
        charge model (TraceT.run ((untilZeroCost xs).run (m := TraceT Id))).2) :=
  (untilZeroCost xs).cost_eq_trace model initial

def conditional (n : ℕ) := if n = 0 then 7 else n / 2
derive_costed conditional as conditionalCost
example : (conditionalCost 0).program.events = [.integer ⟨.eq, [0, 0], 1⟩] := rfl
example : (conditionalCost 8).program.events =
    [.integer ⟨.eq, [8, 0], 0⟩, .integer ⟨.floorDiv, [8, 2], 4⟩] := rfl

def signedFormula (I : Type) [PythonInt I] (x : I) := x * 2 - 1
derive_costed signedFormula as signedCost
example (I : Type) [PythonInt I] (x : I) :
    Id.run ((signedCost I x).run (m := Id)) = signedFormula I x :=
  (signedCost I x).run_id

-- A registered helper can also be called across module boundaries.
def useValuation (I : Type) [PythonInt I] (n k : I) :=
  SympyBinomial.PrimeExponent.valuation I n k + k
derive_costed useValuation as useValuationCost

example (I : Type) [PythonInt I] (n k : I) :
    (useValuationCost I n k).program.events.length = 7 := rfl

-- Even an extensionally identical but unregistered implementation is rejected.
@[instance_reducible]
def hiddenAdd : HAdd ℕ ℕ ℕ := ⟨fun a b => let _unused := a * a; a + b⟩
def changedInstance (n k : ℕ) := @HAdd.hAdd ℕ ℕ ℕ hiddenAdd n k

def unknown (n : ℕ) := n + 1
def unknownCaller (n : ℕ) := unknown n

/--
error: instrumentation: resolved call @HAdd.hAdd does not match contract Checked.natAdd (including its instances)
-/
#guard_msgs in
derive_costed changedInstance as changedInstanceCost

@[instance_reducible]
def otherPure : Pure Id := ⟨fun a => a⟩
def changedPure (n : ℕ) : ℕ := Id.run (@Pure.pure Id otherPure ℕ n)

/--
error: instrumentation: resolved call @pure does not match contract @Checked.idPure (including its instances)
-/
#guard_msgs in
derive_costed changedPure as changedPureCost

/--
error: instrumentation: unsupported call or expression unknown n
Add an explicit operation contract; unknown work is never charged as zero.
-/
#guard_msgs in
derive_costed unknownCaller as unknownCallerCost

def unsupportedWhile (n : ℕ) := Id.run do
  let mut a := n
  while a > 0 do
    a := a - 1
  return a

/-- error: instrumentation: this loop needs a supported iteration contract -/
#guard_msgs in
derive_costed unsupportedWhile as unsupportedWhileCost

-- Inlining this binding at its two uses would duplicate the condition.
def computedClosure (n : ℕ) :=
  let f : ℕ → ℕ := if n < 3 then (fun x => x + 1) else (fun x => x * 2)
  f n + f n

/-- error: instrumentation: computed function bindings need a contract -/
#guard_msgs in
derive_costed computedClosure as computedClosureCost

def signedDivision (x : ℤ) := x.fdiv (-2)
derive_costed signedDivision as signedDivisionCost
example : (signedDivisionCost 7).program.events =
    [.integer ⟨.neg, [2], -2⟩, .integer ⟨.floorDiv, [7, -2], -4⟩] := rfl

#print axioms Checked.cost_eq_trace
#print axioms SympyBinomial.PrimeExponent.valuationInstrumented
#print axioms untilZeroCost

end InstrumentationTests
