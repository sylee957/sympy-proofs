module

public import SympyProofs.Python.Cost.Instrumentation.Derive
public meta import Lean

/-!
# Shared monadic translation infrastructure

Handlers receive a `Translator` callback. This keeps the import graph acyclic
while sharing the evaluation-order and primitive-execution helpers.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

structure DerivedCall where
  target : Name
  parameterCount : Nat
  deriving Inhabited

private def addCall (s : NameMap DerivedCall) (e : Name × DerivedCall) := s.insert e.1 e.2
initialize monadicExt : SimplePersistentEnvExtension (Name × DerivedCall) (NameMap DerivedCall) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addCall
    addImportedFn := mkStateFromImportedEntries addCall {} }

private def addGenerator (s : NameMap Name) (e : Name × Name) := s.insert e.1 e.2
initialize generatorExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addGenerator
    addImportedFn := mkStateFromImportedEntries addGenerator {} }

structure Context where
  monad : Expr
  /-- Explicit translations of source calls, including recursive calls. -/
  calls : NameMap Name := {}
  streams : NameMap Name := {}
  localCalls : FVarIdMap Expr := {}
  /-- Proof-dependent indices retain their source expressions, as termination measures do. -/
  preserveIndexLets : Bool := false
  yieldPrime : Option Expr := none

def pureM (ctx : Context) (value : Expr) : MetaM Expr :=
  mkAppOptM ``Pure.pure #[some ctx.monad, none, none, some value]

def bindM (ctx : Context) (p x body : Expr) : MetaM Expr := do
  if p.isAppOfArity ``Pure.pure 4 then
    return body.replaceFVar x p.getAppArgs[3]!
  let reduced ← whnf p
  if reduced.isAppOfArity ``Pure.pure 4 then
    return body.replaceFVar x reduced.getAppArgs[3]!
  mkAppOptM ``Bind.bind
    #[some ctx.monad, none, none, none, some p, some (← mkLambdaFVars #[x] body)]

private partial def runProgram (ctx : Context) (program : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf program
  let args := reduced.getAppArgs
  if reduced.isAppOfArity ``Program.pure 2 then
    return ← pureM ctx args[1]!
  if reduced.isAppOfArity ``Program.primitive 3 then
    return ← mkAppOptM ``perform
      #[some ctx.monad, none, none, some args[0]!, some args[1]!, some args[2]!]
  if reduced.isAppOfArity ``Program.bind 4 then
    let first ← runProgram ctx args[2]!
    return ← withLocalDeclD `value args[0]! fun x => do
      bindM ctx first x (← runProgram ctx (mkApp args[3]! x))
  mkAppOptM ``Program.run #[some ctx.monad, none, none, none, some program]

def runChecked (ctx : Context) (checked : Expr) : MetaM Expr := do
  runProgram ctx (← mkAppM ``Checked.program #[checked])


/-- Recursive translation passed to handlers, so they do not depend on the dispatcher. -/
abbrev Translator := Context → Expr → MetaM Expr

/-- Sequence runtime operands once, from left to right. -/
partial def operands (recur : Translator) (ctx : Context) (todo done : Array Expr)
    (finish : Array Expr → MetaM Expr) : MetaM Expr := do
  if todo.isEmpty then return ← finish done
  let value := todo[0]!
  let p ← recur ctx value
  withLocalDeclD `arg (← inferType value) fun x => do
    bindM ctx p x (← operands recur ctx (todo.extract 1 todo.size) (done.push x) finish)

/-- Translate runtime call arguments, retaining types, instances and proofs. -/
partial def callArguments (recur : Translator) (ctx : Context) (todo done : Array Expr)
    (finish : Array Expr → MetaM Expr) : MetaM Expr := do
  if todo.isEmpty then return ← finish done
  let value := todo[0]!
  let type ← inferType value
  if (← isProp type) || (← whnf type).isSort || (← isClass? type).isSome then
    return ← callArguments recur ctx (todo.extract 1 todo.size) (done.push value) finish
  let p ← recur ctx value
  if ← isDefEq p (← pureM ctx value) then
    return ← callArguments recur ctx (todo.extract 1 todo.size) (done.push value) finish
  withLocalDeclD `arg type fun x => do
    bindM ctx p x (← callArguments recur ctx (todo.extract 1 todo.size) (done.push x) finish)

end Python.Cost.Instrumentation.Monadic
