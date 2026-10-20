module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public import SympyProofs.Python.Cost.Instrumentation.Storage
public import SympyProofs.Python.Cost.Generator
public meta import Lean

/-!
# Loops and generator suspension

Stream adapters must match a previously generated producer, including its
events and deferred execution.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

/-- Preserve suspension and charge yield and resume separately. -/
def translateYield (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let some yieldPrime := ctx.yieldPrime
    | throwError "instrumentation: yield outside a generator contract"
  return ← operands recur ctx #[args[1]!] #[] fun values => do
    let action := mkApp yieldPrime values[0]!
    let before ← mkAppOptM ``MonadCost.emit
      #[some ctx.monad, none, some (← mkAppM ``Event.control #[mkStrLit "generator.yield"])]
    let after ← mkAppOptM ``MonadCost.emit
      #[some ctx.monad, none, some (← mkAppM ``Event.control #[mkStrLit "generator.resume"])]
    withLocalDeclD `unit (mkConst ``Unit) fun u => do
      bindM ctx before u (← bindM ctx action u after)

/-- Translate the audited dependent generator range. -/
def translateRange (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  unless args[1]! == mkConst ``Std.Legacy.Range do
    throwError "instrumentation: unsupported dependent iterator"
  unless args[0]!.isAppOfArity ``Generator.Computation 1 do
    throwError "instrumentation: unsupported dependent source monad"
  let expected ← mkAppOptM ``Source.generatorRange
    #[some args[0]!.appArg!, some args[5]!, some args[6]!, some args[7]!, some args[8]!]
  unless ← sameResolved (aliases e) (aliases (← unfoldDefinition expected)) do
    throwError "instrumentation: unsupported dependent range instance"
  let body ← lambdaTelescope args[8]! fun ps body => do
    unless ps.size == 3 do throwError "instrumentation: unsupported dependent body"
    let result ← recur ctx body
    if result.containsFVar ps[1]!.fvarId! then
      throwError "instrumentation: range membership proof escaped its erased arguments"
    let emit ← mkAppOptM ``MonadCost.emit
      #[some ctx.monad, none, some (← mkAppM ``Event.control #[mkStrLit "sieve.next"])]
    let result ← withLocalDeclD `unit (mkConst ``Unit) fun u => bindM ctx emit u result
    mkLambdaFVars #[ps[0]!, ps[2]!] result
  return ← operands recur ctx #[args[6]!, args[7]!] #[] fun values => do
    let loop ← mkAppOptM ``ForIn.forIn #[some ctx.monad, none, some args[2]!, none,
      some args[5]!, some values[0]!, some values[1]!, some body]
    withLocalDeclD `state args[5]! fun state => do
      let emit ← mkAppOptM ``MonadCost.emit
        #[some ctx.monad, none, some (← mkAppM ``Event.control #[mkStrLit "sieve.stop"])]
      let result ← withLocalDeclD `unit (mkConst ``Unit) fun u => do
        bindM ctx emit u (← pureM ctx state)
      bindM ctx loop state result

/-- Translate audited list, while-loop and lazy-stream iteration. -/
def translateForIn (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let collection := args[5]!
  if args[1]!.isAppOfArity ``List 1 then
    return ← runChecked ctx (← Instrumentation.translate e)
  let expected ←
    if args[1]! == mkConst ``Lean.Loop then
      if args[0]! == mkConst ``Id [0] then
        mkAppOptM ``Source.idLoop #[some args[4]!, some args[6]!, some args[7]!]
      else if args[0]!.isAppOfArity ``Generator.Computation 1 then
        mkAppOptM ``Source.generatorLoop
          #[some args[0]!.appArg!, some args[4]!, some args[6]!, some args[7]!]
      else throwError "instrumentation: unsupported while-loop source monad"
    else if ctx.streams.contains (collection.getAppFn.constName?.getD .anonymous) then
      mkAppOptM ``Source.idStream
        #[some args[2]!, some args[4]!, some collection, some args[6]!, some args[7]!]
    else throwError "instrumentation: unsupported iterator"
  unless ← sameResolved (aliases e) (aliases (← unfoldDefinition expected)) do
    throwError "instrumentation: unsupported iterator instance"

  let isStream := ctx.streams.contains (collection.getAppFn.constName?.getD .anonymous)
  let body ← lambdaTelescope args[7]! fun params body => do
    let body ← recur ctx body
    let body ← if isStream then do
      let event ← mkAppM ``Event.control #[mkStrLit "for.next"]
      let emit ← mkAppOptM ``MonadCost.emit #[some ctx.monad, none, some event]
      withLocalDeclD `unit (mkConst ``Unit) fun x => bindM ctx emit x body
    else pure body
    mkLambdaFVars params body
  if let some target := ctx.streams.find? (collection.getAppFn.constName?.getD .anonymous) then
    return ← callArguments recur ctx collection.getAppArgs #[] fun values => do
      let stream ← mkAppOptM target (values.map some)
      let some generated := generatorExt.getState (← getEnv) |>.find? (collection.getAppFn.constName?.getD .anonymous)
        | throwError "instrumentation: stream mapping requires a generated source definition"
      let entryType ← mkAppM ``Sum #[mkConst ``Event, args[2]!]
      let producerMonad ← mkAppM ``Generator.Computation #[entryType]
      let yieldValue ← withLocalDeclD `value args[2]! fun x => do
        let entry ← mkAppOptM ``Sum.inr #[some (mkConst ``Event), some args[2]!, some x]
        mkLambdaFVars #[x] (← mkAppM ``Generator.yield #[entry])
      let cost ← mkAppOptM ``eventCost #[some args[2]!]
      let producer ← mkAppOptM generated
        (values.map some ++ #[some producerMonad, none, some cost, none, some yieldValue])
      let deferred ← withLocalDeclD `unit (mkConst ``Unit) fun u => do
        mkAppM ``Generator.create #[← mkLambdaFVars #[u] producer]
      let expected ← mkAppM ``Stream.mk #[deferred]
      unless ← isDefEq stream expected do
        throwError "instrumentation: stream adapter does not match the generated producer"
      operands recur ctx #[args[6]!] #[] fun values => do
        let loop ← mkAppOptM ``ForIn.forIn #[some ctx.monad, none, some args[2]!,
          none, some args[4]!, some stream, some values[0]!, some body]
        withLocalDeclD `result args[4]! fun x => do
          let event ← mkAppM ``Event.control #[mkStrLit "for.stop"]
          let emit ← mkAppOptM ``MonadCost.emit #[some ctx.monad, none, some event]
          let ret ← withLocalDeclD `unit (mkConst ``Unit) fun u => do
            bindM ctx emit u (← pureM ctx x)
          bindM ctx loop x ret
  return ← operands recur ctx #[args[5]!, args[6]!] #[] fun values =>
    mkAppOptM ``ForIn.forIn #[some ctx.monad, some args[1]!, some args[2]!,
      none, some args[4]!, some values[0]!, some values[1]!, some body]

end Python.Cost.Instrumentation.Monadic
