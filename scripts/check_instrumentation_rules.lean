import SympyProofs.Python.Cost.Instrumentation.Monadic

/-! Run with `lake env lean scripts/check_instrumentation_rules.lean`.
These checks add a carrier and two independently registered rule sets without
modifying the translators. They also exercise imported storage rules.
-/

open Lean Meta
open Python.Cost Python.Cost.Instrumentation

namespace InstrumentationRuleTests

structure Box where
  value : Nat

instance : Add Box := ⟨fun a b => ⟨a.value + b.value⟩⟩

def boxAdd (a b : Box) : Checked (a + b) :=
  Checked.primitive (.control "box.add") _

meta def boxPattern : CallPattern :=
  .both (.capture `left) (.typed .any
    (.orElse (CallPattern.const ``String) (CallPattern.const ``Box)))

meta def boxRules : OperationRules := #[
  { pattern := .tail ``HAdd.hAdd #[boxPattern, .capture `right]
    contract := ``boxAdd, operands := #[`left, `right] }
]

register_cost_rules boxRules

def combine (a b : Box) := Id.run do
  let shared := a + b
  return shared + shared

derive_costed combine as combineChecked
derive_costed_monadic combine as combineMonadic using [] streams []

example (a b : Box) :
    (combineChecked a b).program.events = [.control "box.add", .control "box.add"] := rfl

example (a b : Box) :
    TraceT.run (combineMonadic a b (m := TraceT Id)) =
      (combine a b, [.control "box.add", .control "box.add"]) := rfl

example (a b : Box) : Id.run (combineMonadic a b (m := Id)) = combine a b := rfl

-- A second, unrelated parser group composes with the first one.
def inspectBox (a : Box) : Nat := a.value
def inspectContract (a : Box) : Checked (inspectBox a) :=
  Checked.primitive (.control "box.inspect") _

meta def inspectRules : OperationRules := #[
  OperationRule.unary ``inspectBox ``inspectContract
]

register_cost_rules inspectRules

def inspectSum (a b : Box) := inspectBox (a + b)
derive_costed inspectSum as inspectSumChecked
derive_costed_monadic inspectSum as inspectSumMonadic using [] streams []

example (a b : Box) : (inspectSumChecked a b).program.events =
    [.control "box.add", .control "box.inspect"] := rfl
example (a b : Box) : TraceT.run (inspectSumMonadic a b (m := TraceT Id)) =
    (inspectSum a b, [.control "box.add", .control "box.inspect"]) := rfl

-- Neither matching notation nor having the correct result licenses a changed instance.
@[instance_reducible]
def otherAdd : HAdd Box Box Box := ⟨fun a b => a + b⟩
def changed (a b : Box) := @HAdd.hAdd Box Box Box otherAdd a b

/--
error: instrumentation: resolved call @HAdd.hAdd does not match contract boxAdd (including its instances)
-/
#guard_msgs in
derive_costed changed as changedChecked

/--
error: instrumentation: resolved call @HAdd.hAdd does not match contract boxAdd (including its instances)
-/
#guard_msgs in
derive_costed_monadic changed as changedMonadic using [] streams []

-- The registry came through imported modules; both interpreters use the same
-- bytearray rules, and arithmetic inside its operands is still counted once.
def repeatLength (B : Type) [PythonByteArray B] (bytes : B) (n : Nat) :=
  PythonByteArray.Value.len (bytes * (n + 1))

derive_costed repeatLength as repeatLengthChecked
derive_costed_monadic repeatLength as repeatLengthMonadic using [] streams []

example (B : Type) [PythonByteArray B] (bytes : B) (n : Nat) :
    TraceT.run (repeatLengthMonadic B bytes n (m := TraceT Id)) =
      ((repeatLengthChecked B bytes n).program.value,
        (repeatLengthChecked B bytes n).program.events) := rfl

-- Exact-arity matching rejects partial calls without inspecting nonexistent arguments.
run_meta do
  let result ← (CallPattern.app ``inspectBox #[.capture `box]).parse (mkConst ``inspectBox)
  unless result.isNone do throwError "a partial call unexpectedly matched"

-- An extension cannot conceal a computation in the static parameter list.
/-- error: instrumentation: parameter value is runtime data; declare it as an operand -/
#guard_msgs in
run_meta do
  let rule : OperationRule := {
    pattern := .capture `value
    contract := ``Checked.natSqrt
    operands := #[]
    parameters := #[some `value] }
  let _ ← rule.parse (mkNatLit 4)

-- Audit failure is terminal: the later valid rule must not hide a broken earlier rule.
def secret (n : Nat) := n + 1
def secretContract (n : Nat) : Checked (secret n) := Checked.primitive (.control "secret") _
meta def invalidRules : OperationRules := #[
  { pattern := .app ``secret #[.capture `n]
    contract := ``Checked.natSqrt, operands := #[`n] },
  { pattern := .app ``secret #[.capture `n]
    contract := ``secretContract, operands := #[`n] }
]
register_cost_rules invalidRules

def useSecret (n : Nat) := secret n
/--
error: instrumentation: resolved call secret does not match contract Checked.natSqrt (including its instances)
-/
#guard_msgs in
derive_costed useSecret as useSecretChecked

#print axioms combineChecked
#print axioms combineMonadic

end InstrumentationRuleTests
