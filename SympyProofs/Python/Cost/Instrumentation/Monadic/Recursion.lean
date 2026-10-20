module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public meta import Lean

/-!
# Well-founded recursion and registered helper calls

The source measure and decrease proofs are retained. Recursive arguments
must package already evaluated values; helper adapters must preserve effects.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

/-- Recursive arguments must only package already evaluated values. Arithmetic
belongs in an instrumented binding, so it cannot disappear inside a proof argument. -/
partial def recursiveData (e : Expr) : MetaM Bool := do
  if ← isProof e then return true
  match e.consumeMData with
  | .fvar _ | .lit _ => return true
  | .proj _ _ value => recursiveData value
  | _ =>
    if e.isAppOfArity ``PSigma.mk 4 then
      return (← recursiveData e.getAppArgs[2]!) && (← recursiveData e.getAppArgs[3]!)
    if e.isAppOfArity ``OfNat.ofNat 3 then
      return e.getAppArgs[0]! == mkConst ``Nat && e.getAppArgs[1]!.isRawNatLit &&
        e.getAppArgs[2]! == mkApp (mkConst ``instOfNatNat) e.getAppArgs[1]!
    return false

/-- Retain Lean's well-founded measure and decrease proofs, translating its step body. -/
def translateFix (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let sourceMotive := args[1]!
  let targetMotive ← withLocalDeclD `state args[0]! fun x =>
    mkLambdaFVars #[x] (mkApp ctx.monad (mkApp sourceMotive x))
  let body ← lambdaTelescope args[3]! fun outer body => do
    unless outer.size == 2 do throwError "instrumentation: unsupported well-founded step"
    let state := outer[0]!
    let recType ← forallTelescope (← inferType outer[1]!) fun ps result =>
      mkForallFVars ps (mkApp ctx.monad result)
    withLocalDeclD `recurse recType fun recurse => do
      let raw := body.consumeMData
      let caseArgs := raw.getAppArgs
      unless raw.isAppOfArity ``PSigma.casesOn 6 do
        throwError "instrumentation: well-founded state must use PSigma.casesOn"
      let branch ← lambdaTelescope caseArgs[4]! fun ps inner => do
        unless ps.size == 3 do throwError "instrumentation: expected a two-field recursive state"
        let innerType ← forallTelescope (← inferType ps[2]!) fun ys result =>
          mkForallFVars ys (mkApp ctx.monad result)
        withLocalDeclD `recurse innerType fun innerRec => do
          let oldId := ps[2]!.fvarId!
          let localCalls := ctx.localCalls.insert oldId innerRec
          let innerCtx := { ctx with localCalls := localCalls, preserveIndexLets := true }
          let translated ← recur innerCtx inner
          mkLambdaFVars (ps.extract 0 2 |>.push innerRec) translated
      let motive ← mkLambdaFVars #[state] (← mkArrow recType (mkApp targetMotive state))
      let result ← mkAppOptM ``PSigma.casesOn
        #[some caseArgs[0]!, some caseArgs[1]!, some motive, some state, some branch]
      mkLambdaFVars #[state, recurse] (mkApp result recurse)
  mkAppOptM ``WellFounded.Nat.fix
    #[some args[0]!, some targetMotive, some args[2]!, some body]

/-- Check a registered helper mapping and translate its arguments. -/
def translateCall (recur : Translator) (ctx : Context) (e : Expr) (target : Name) : MetaM Expr := do
  let args := e.getAppArgs
  return ← callArguments recur ctx args #[] fun values => do
    let some derived := monadicExt.getState (← getEnv) |>.find? (e.getAppFn.constName?.getD .anonymous)
      | throwError "instrumentation: helper mapping requires a generated source definition"
    let front := values.extract 0 derived.parameterCount
    let rest := values.extract derived.parameterCount values.size
    let expected ← mkAppOptM derived.target
      (front.map some ++ #[some ctx.monad, none, none] ++ rest.map some)
    if target == derived.target then return expected
    let result ← mkAppOptM target (values.map some ++ #[some ctx.monad, none, none])
    unless ← isDefEq result expected do
      throwError "instrumentation: helper adapter does not match the generated computation"
    pure result

end Python.Cost.Instrumentation.Monadic
