module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Control
public import SympyProofs.Python.Cost.Instrumentation.Monadic.Iteration
public import SympyProofs.Python.Cost.Instrumentation.Monadic.Primitives
public import SympyProofs.Python.Cost.Instrumentation.Monadic.Recursion
public meta import Lean

/-!
# Dispatcher for elaborated monadic expressions

This traversal handles binding and structural expressions. Ordinary operations
use the shared rule registry; specialized execution adapters receive recursive
translation as a callback.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

partial def translate (ctx : Context) (original : Expr) : MetaM Expr := do
  let e := aliases original
  match e with
  | .letE name type value body _ =>
    if (← isProp type) then
      translate ctx (body.instantiate1 value)
    else if (← whnf type).isForall then
      unless value.consumeMData.isLambda do
        throwError "instrumentation: computed function bindings need a contract"
      translate ctx (body.instantiate1 value)
    else
      let p ← translate ctx value
      if ctx.preserveIndexLets && (← isDefEq type (mkConst ``Nat)) then
        return ← withLetDecl name type value fun x => do
          let body ← mkLetFVars #[x] (← translate ctx (body.instantiate1 x))
          withLocalDeclD `ignored type fun ignored => bindM ctx p ignored body
      withLocalDeclD name type fun x => do
        bindM ctx p x (← translate ctx (body.instantiate1 x))
  | .proj structureName index value =>
    let p ← translate ctx value
    withLocalDeclD `record (← inferType value) fun x => do
      bindM ctx p x (← pureM ctx (.proj structureName index x))
  | _ =>
    let args := e.getAppArgs
    if e.isAppOfArity ``Id.run 2 then
      return ← translate ctx args[1]!
    if e.isAppOfArity ``Pure.pure 4 then
      return ← translatePure translate ctx e
    if e.isAppOfArity ``Bind.bind 6 then
      return ← translateBind translate ctx e
    if e.isAppOfArity ``ite 5 then
      return ← translateBranch translate ctx e
    if e.isAppOfArity ``Generator.yield 2 then
      return ← translateYield translate ctx e
    if e.isAppOfArity ``ForIn'.forIn' 9 then
      return ← translateRange translate ctx e
    if e.isAppOfArity ``Std.Legacy.Range.mk 4 then
      return ← operands translate ctx (args.extract 0 3) #[] fun values =>
        pureM ctx (mkAppN e.getAppFn (values.push args[3]!))
    if let some operation ← parseOperation e (monadic := true) then
      return ← translateOperation translate ctx operation
    if e.isAppOfArity ``PythonByteArray.Value.setSlice 8 then
      return ← translateSlice translate ctx e
    if e.isAppOfArity ``dite 5 then
      return ← translateDependentBranch translate ctx e
    if e.isAppOfArity ``WellFounded.Nat.fix 4 then
      return ← translateFix translate ctx e
    if e.isAppOf ``Python.Math.prod then
      return ← translateProd translate ctx e
    if let .fvar id := e.getAppFn then
      if let some target := ctx.localCalls.get? id then
        for arg in args do
          unless ← recursiveData arg do
            throwError "instrumentation: bind computed recursive arguments before the call"
        -- The proof arguments are reused verbatim with the original decreasing measure.
        return mkAppN target args
    if e.isAppOfArity ``ForIn.forIn 8 then
      return ← translateForIn translate ctx e
    if e.isAppOfArity ``Prod.mk 4 || e.isAppOfArity ``PSigma.mk 4 then
      return ← operands translate ctx (args.extract 2 4) #[] fun values =>
        pureM ctx (mkAppN e.getAppFn (args.extract 0 2 ++ values))
    if e.isAppOfArity ``ForInStep.yield 2 || e.isAppOfArity ``ForInStep.done 2 then
      return ← operands translate ctx #[args[1]!] #[] fun values =>
        pureM ctx (mkApp2 e.getAppFn args[0]! values[0]!)
    if e.isAppOfArity ``Lean.Loop.mk 0 then return ← pureM ctx e
    if e.isAppOf ``Nat.cast || e.isAppOf ``Int.cast then
      return ← translateCast translate ctx e
    if e.isAppOf ``PythonInt.toNat || e.isAppOf ``PythonInt.Value.toNat ||
        e.isAppOf ``Int.toNat then
      let index :=  args.size - 1
      return ← operands translate ctx #[args[index]!] #[] fun values =>
        pureM ctx (mkAppN e.getAppFn (args.set! index values[0]!))
    if e.isAppOfArity ``Array.emptyWithCapacity 2 then
      unless args[1]!.isRawNatLit do
        throwError "instrumentation: dynamic array capacity requires a contract"
      return ← mkAppOptM ``Sequence.empty #[some ctx.monad, none, none, some args[0]!]
    if e.isAppOfArity ``List.toArray 2 && args[1]!.isAppOfArity ``List.nil 1 then
      return ← mkAppOptM ``Sequence.empty #[some ctx.monad, none, none, some args[0]!]
    if e.isAppOfArity ``Array.push 3 then
      return ← operands translate ctx (args.extract 1 3) #[] fun values =>
        mkAppOptM ``Sequence.append #[some ctx.monad, none, none,
          some args[0]!, some values[0]!, some values[1]!]
    if let .lam name type body _ := e.getAppFn then
      if args.isEmpty then throwError "instrumentation: unsupported function value"
      let p ← translate ctx args[0]!
      return ← withLocalDeclD name type fun x => do
        bindM ctx p x (← translate ctx
          (mkAppN (body.instantiate1 x) (args.extract 1 args.size)))
    if let some target := ctx.calls.find? (e.getAppFn.constName?.getD .anonymous) then
      return ← translateCall translate ctx e target
    runChecked ctx (← Instrumentation.translate e)

end Python.Cost.Instrumentation.Monadic
