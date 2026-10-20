module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public import SympyProofs.Python.Cost.Instrumentation.Storage
public import SympyProofs.Python.Cost.Sequence
public import SympyProofs.Python.Cost.BufferIndex
public meta import Lean

/-!
# Monadic primitive and storage translation

Ordinary operation recognition is shared with the finite backend through
`Instrumentation.Rules` and its independently registered rule modules.
This module interprets those results and retains the execution adapters for
proof-dependent slice assignment, product calls and representation casts.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

/-- Interpret a recognized operation; parsing is shared with the finite backend. -/
def translateOperation (recur : Translator) (ctx : Context)
    (operation : ParsedOperation) : MetaM Expr :=
  operands recur ctx operation.operands #[] fun values => do
    runChecked ctx (← operation.checked values)

/-- Slice assignment retains its proof-dependent execution adapter. -/
def translateSlice (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  auditPrimitive (mkAppN e.getAppFn (args.extract 0 2))
    (← mkAppOptM ``Checked.sliceCall #[some args[0]!, some args[1]!])
  operands recur ctx (args.extract 2 6) #[] fun values =>
    mkAppOptM ``BufferIndex.setSlice
      (#[some args[0]!, some args[1]!, some ctx.monad, none, none] ++ values.map some)

/-- Audit `Python.Math.prod` and use its costed implementation. -/
def translateProd (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  auditPrimitive e (← mkAppM ``Checked.prodCall #[args.back!])
  return ← operands recur ctx #[args.back!] #[] fun values =>
    mkAppOptM ``Sequence.prod #[some ctx.monad, none, none, none, none, some values[0]!]

/-- Audit representation casts and translate their operand. -/
def translateCast (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let type ← inferType e
  let contract := if e.isAppOf ``Int.cast then ``Checked.pyIntCast
    else if type == mkConst ``Int then ``Checked.intNatCast else ``Checked.pyNatCast
  let make (value : Expr) := if contract == ``Checked.intNatCast then
    mkAppM contract #[value]
    else mkAppOptM contract #[some type, none, some value]
  auditPrimitive e (← make args.back!)
  return ← operands recur ctx #[args.back!] #[] fun values => do
    runChecked ctx (← make values[0]!)

end Python.Cost.Instrumentation.Monadic
