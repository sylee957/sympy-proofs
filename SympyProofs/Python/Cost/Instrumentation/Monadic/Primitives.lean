module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public import SympyProofs.Python.Cost.Instrumentation.Storage
public import SympyProofs.Python.Cost.Sequence
public import SympyProofs.Python.Cost.BufferIndex
public meta import Lean

/-!
# Monadic primitive and storage translation

Resolved operations are checked against the existing primitive contracts.
The contracts themselves remain in `Instrumentation.Primitives` and
`Instrumentation.Storage`.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

/-- Recognize and audit byte and bytearray operations; `none` means no match. -/
def storage (recur : Translator) (ctx : Context) (e : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  if e.isAppOfArity ``OfNat.ofNat 3 && args[0]! == mkConst ``UInt8 then
    let checked ← mkAppM ``Checked.byteNumeral #[args[1]!]
    auditPrimitive e checked
    return some (← runChecked ctx checked)
  if e.isAppOf ``Neg.neg && args.back!.isAppOfArity ``OfNat.ofNat 3 &&
      (← inferType e) == mkConst ``Int then
    let checked ← mkAppM ``Checked.negativeLiteral #[args.back!.getAppArgs[1]!]
    auditPrimitive e checked
    return some (← runChecked ctx checked)
  if e.isAppOfArity ``PythonByteArray.Value.setSlice 8 then
    auditPrimitive (mkAppN e.getAppFn (args.extract 0 2))
      (← mkAppOptM ``Checked.sliceCall #[some args[0]!, some args[1]!])
    return some (← operands recur ctx (args.extract 2 6) #[] fun values =>
      mkAppOptM ``BufferIndex.setSlice
        (#[some args[0]!, some args[1]!, some ctx.monad, none, none] ++ values.map some))
  let (contract, values, explicit) ←
    if e.isAppOf ``bytearray then
      pure (``Checked.byteOfBytes, #[args.back!], #[args[0]!, args[1]!])
    else if e.isAppOf ``PythonByteArray.Value.len then
      pure (``Checked.byteLength, #[args.back!], #[])
    else if e.isAppOf ``PythonByteArray.Value.set! then
      pure (``Checked.byteSet, args.extract 2 5, #[])
    else if e.isAppOf ``PythonByteArray.Value.find then
      pure (``Checked.byteFind, args.extract 2 5, #[])
    else if e.isAppOf ``GetElem?.getElem! then
      pure (``Checked.byteGet, args.extract (args.size - 2) args.size, #[])
    else if e.isAppOf ``PythonBytes.literal && args[0]!.isAppOf ``PythonByteArray.Bytes then
      let bytes := args.back!
      unless bytes.isAppOfArity ``List.toArray 2 && bytes.appArg!.isAppOfArity ``List.cons 3 &&
          bytes.appArg!.getAppArgs[2]!.isAppOf ``List.nil do
        throwError "instrumentation: only singleton bytes literals have a contract"
      pure (``Checked.byteLiteral, #[bytes.appArg!.getAppArgs[1]!], args[0]!.getAppArgs)
    else if e.isAppOf ``HMul.hMul && args[0]!.isAppOf ``PythonByteArray.Bytes then
      pure (``Checked.bytesRepeat, args.extract 4 6, args[0]!.getAppArgs)
    else if e.isAppOf ``HMul.hMul then
      let .some _ ← trySynthInstance (← mkAppM ``PythonByteArray #[args[0]!]) | return none
      pure (``Checked.byteRepeat, args.extract 4 6, #[])
    else return none
  let make (values : Array Expr) : MetaM Expr :=
    if explicit.isEmpty then mkAppM contract values
    else mkAppOptM contract ((explicit ++ values).map some)
  auditPrimitive e (← make values)
  return some (← operands recur ctx values #[] fun values => do runChecked ctx (← make values))

/-- Audit and charge array length. -/
def translateArraySize (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let checked ← mkAppM ``Checked.arraySize #[args[1]!]
  auditPrimitive e checked
  return ← operands recur ctx #[args[1]!] #[] fun values => do
    runChecked ctx (← mkAppM ``Checked.arraySize values)

/-- Audit and charge materialization of an array slice. -/
def translateArraySlice (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let values := args.back!.getAppArgs.extract 1 4
  let checked ← mkAppM ``Checked.arraySlice values
  auditPrimitive e checked
  return ← operands recur ctx values #[] fun values => do
    runChecked ctx (← mkAppM ``Checked.arraySlice values)

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

/-- Translate an audited arithmetic primitive or fall back to the finite checked backend. -/
def translatePrimitive (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if let some (contract, arity) ← Instrumentation.primitive? e then
    let head := mkAppN e.getAppFn (args.extract 0 (args.size - arity))
    return ← operands recur ctx (args.extract (args.size - arity) args.size) #[] fun values => do
      let checked ← mkAppM contract values
      auditPrimitive (mkAppN head values) checked
      runChecked ctx checked
  -- This path has a checked value certificate and audited instances.
  runChecked ctx (← Instrumentation.translate e)

end Python.Cost.Instrumentation.Monadic
