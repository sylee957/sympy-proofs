module

public import SympyProofs.Python.Cost.Instrumentation.Audit
public meta import Lean

/-!
# Composable operation recognition

Rules describe resolved calls using named captures, nested application patterns,
type guards and alternatives. Only the pattern interpreter inspects `Expr`.
Rule modules select an existing `Checked` contract and list its runtime operands
in evaluation order; they do not implement translation or cost emission.

`register_cost_rules rules` adds an independently defined `OperationRules` to both
instrumentation backends. Imports preserve registrations. Rules are tried in
registration order, then array order. A nonmatch rolls back metavariable changes;
a matched rule whose contract fails the audit is an error, never a fallback.

This is a frontend for elaborated Lean, so overloaded notation and macros have
already been resolved. It is not a parser for Python text or a verified compiler.
The contract audit and kernel-checked value certificates remain separate.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation

/-- Patterns compose without exposing expression argument positions to rule authors. -/
inductive CallPattern where
  | any
  | bind (name : Name) (pattern : CallPattern)
  /-- Match a fully applied head with exactly these arguments. -/
  | app (head : Name) (arguments : Array CallPattern)
  /-- Match the last arguments of a head, leaving its implicit parameters to the audit. -/
  | tail (head : Name) (arguments : Array CallPattern)
  | typed (value type : CallPattern)
  /-- The matched expression is a type with this class instance. -/
  | instanceOf (className : Name)
  | both (first second : CallPattern)
  | orElse (first second : CallPattern)
  deriving Inhabited

namespace CallPattern

def capture (name : Name) (pattern : CallPattern := .any) : CallPattern := .bind name pattern

def const (name : Name) : CallPattern := .app name #[]

def singletonArray (value : CallPattern) : CallPattern :=
  .app ``List.toArray #[.any, .app ``List.cons #[.any, value, .app ``List.nil #[.any]]]

private partial def matchCore (pattern : CallPattern) (e : Expr)
    (captures : NameMap Expr) : MetaM (Option (NameMap Expr)) := do
  match pattern with
  | .any => return some captures
  | .bind name pattern =>
    let some captures ← matchCore pattern e captures | return none
    if let some old := captures.find? name then
      if old != e then return none
    return some (captures.insert name e)
  | .app head patterns | .tail head patterns =>
    let args := e.getAppArgs
    unless e.isAppOf head do return none
    match pattern with
    | .app .. => unless args.size == patterns.size do return none
    | _ => unless patterns.size ≤ args.size do return none
    let mut captures := captures
    for p in patterns, arg in args.extract (args.size - patterns.size) args.size do
      let some next ← matchCore p arg captures | return none
      captures := next
    return some captures
  | .typed value type =>
    let some captures ← matchCore value e captures | return none
    matchCore type (aliases (← inferType e)) captures
  | .instanceOf className =>
    let goal ← mkAppM className #[e]
    let .some _ ← trySynthInstance goal | return none
    return some captures
  | .both first second =>
    let some captures ← matchCore first e captures | return none
    matchCore second e captures
  | .orElse first second =>
    let state ← saveState
    if let some result ← matchCore first e captures then return some result
    state.restore
    matchCore second e captures

/-- A failed pattern leaves no metavariable assignments behind. -/
def parse (pattern : CallPattern) (e : Expr) : MetaM (Option (NameMap Expr)) := do
  let state ← saveState
  let result ← matchCore pattern (aliases e) {}
  if result.isNone then state.restore
  return result

end CallPattern

structure OperationRule where
  pattern : CallPattern
  contract : Name
  /-- Named runtime operands, in their source evaluation order. -/
  operands : Array Name
  /-- Explicit contract parameters; `none` asks Lean to infer that parameter. -/
  parameters : Array (Option Name) := #[]
  /-- Some literal policies are specific to the monadic source model. -/
  monadicOnly : Bool := false
  deriving Inhabited

namespace OperationRule

/-- Construct a unary rule directly from its operation and contract.
The optional carrier pattern guards the operand's type. -/
def unary (operation contract : Name) (carrier : CallPattern := .any) : OperationRule :=
  { pattern := .tail operation #[.typed (.capture `x) carrier]
    contract
    operands := #[`x] }

/-- Construct a binary rule with left-to-right operand evaluation.
The optional carrier pattern guards the first operand's type. -/
def binary (operation contract : Name) (carrier : CallPattern := .any) : OperationRule :=
  { pattern := .tail operation #[.typed (.capture `x) carrier, .capture `y]
    contract
    operands := #[`x, `y] }

end OperationRule

/-- Backend-independent result of recognition. It contains no interpreter callback. -/
structure ParsedOperation where
  contract : Name
  operands : Array Expr
  parameters : Array (Option Expr)

def ParsedOperation.checked (operation : ParsedOperation) (values : Array Expr) : MetaM Expr := do
  unless values.size == operation.operands.size do
    throwError "instrumentation: incorrect number of parsed operands"
  if operation.parameters.isEmpty then mkAppM operation.contract values
  else mkAppOptM operation.contract (operation.parameters ++ values.map some)

def OperationRule.parse (rule : OperationRule) (e : Expr) : MetaM (Option ParsedOperation) := do
  let some captures ← rule.pattern.parse e | return none
  let get (name : Name) : MetaM Expr :=
    match captures.find? name with
    | some value => pure value
    | none => throwError "instrumentation: rule {rule.contract} has an unbound capture {name}"
  let operands ← rule.operands.mapM get
  let parameters ← rule.parameters.mapM fun name =>
    match name with
    | some name => do
      let value ← get name
      let type ← inferType value
      unless (← isProp type) || (← whnf type).isSort || (← isClass? type).isSome do
        throwError "instrumentation: parameter {name} is runtime data; declare it as an operand"
      return some value
    | none => pure none
  return some ⟨rule.contract, operands, parameters⟩

abbrev OperationRules := Array OperationRule

/-- Lean's standard attribute loader evaluates only declarations of `OperationRules`.
The unsafe initialization is confined to this metaprogram registry; generated
definitions and proofs still go through `addDecl` and the kernel. -/
unsafe initialize operationRulesAttribute : KeyedDeclsAttribute OperationRules ←
  KeyedDeclsAttribute.init {
    name := `cost_rules
    descr := "Register composable cost operation rules"
    valueTypeName := ``OperationRules
    evalKey := fun _ _ => pure .anonymous }

/-- Add a rule module without editing either translator. -/
macro "register_cost_rules " rules:ident : command => `(attribute [cost_rules] $rules)

/-- Compose registered parsers, then audit the selected contract before interpretation. -/
def parseOperation (e : Expr) (monadic : Bool := false) : MetaM (Option ParsedOperation) := do
  for rules in (operationRulesAttribute.getValues (← getEnv) .anonymous).reverse do
    for rule in rules do
      if rule.monadicOnly && !monadic then continue
      if let some operation ← rule.parse e then
        auditPrimitive e (← operation.checked operation.operands)
        return some operation
  return none

end Python.Cost.Instrumentation
