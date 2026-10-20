module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Translate
public meta import Lean

/-!
# Commands for deriving costed definitions

These commands elaborate parameters, invoke the translator, kernel-check
the generated declaration and register it for later helper or stream calls.
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

elab "derive_costed_monadic " source:ident " as " target:ident
    " using " "[" mappings:ident,* "]" " streams " "[" producers:ident,* "]" : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let .defnInfo info ← getConstInfo src
    | throwErrorAt source "instrumentation requires a transparent definition"
  unless info.safety == .safe do
    throwErrorAt source "instrumentation requires a safe definition"
  let dst := (← getCurrNamespace) ++ target.getId
  let mut calls : NameMap Name := {}
  do
    let names := mappings.getElems
    unless names.size % 2 == 0 do throwError "expected pairs of source and generated function names"
    for i in [:names.size / 2] do
      let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo names[2*i]!
      let dst ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo names[2*i+1]!
      calls := calls.insert src dst
  let mut streams : NameMap Name := {}
  do
    let names := producers.getElems
    unless names.size % 2 == 0 do throwError "expected pairs of source and instrumented stream names"
    for i in [:names.size / 2] do
      let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo names[2*i]!
      let dst ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo names[2*i+1]!
      streams := streams.insert src dst
  liftTermElabM do
    let level := `cost_u
    let mType ← mkArrow (mkSort 1) (mkSort (.succ (.param level)))
    let (type, value, parameterCount) ← lambdaTelescope info.value fun params body => do
      withLocalDecl `m .implicit mType fun m => do
      withLocalDecl `instMonad .instImplicit (← mkAppM ``Monad #[m]) fun monad => do
      withLocalDecl `instCost .instImplicit (← mkAppM ``MonadCost #[m]) fun cost => do
        let value ← translate { monad := m, calls, streams } body
        let all := params ++ #[m, monad, cost]
        return (← mkForallFVars all (← inferType value), ← mkLambdaFVars all value, params.size)
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasMVar || value.hasMVar then throwError "instrumentation: unresolved metavariables"
    let decl := Declaration.defnDecl {
      name := dst, levelParams := info.levelParams ++ [level], type, value,
      hints := .regular 0, safety := .safe
    }
    addDecl decl (forceExpose := true)
    enableRealizationsForConst dst
    compileDecl decl
    modifyEnv (monadicExt.addEntry · (src, ⟨dst, parameterCount⟩))


/-- Instrument a generator body without evaluating it or erasing its suspension points. -/
elab "derive_costed_generator " source:ident " as " target:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let .defnInfo info ← getConstInfo src
    | throwError "instrumentation requires a transparent generator definition"
  unless info.safety == .safe do throwError "instrumentation requires a safe definition"
  let dst := (← getCurrNamespace) ++ target.getId
  liftTermElabM do
    let level := `cost_u
    let mType ← mkArrow (mkSort 1) (mkSort (.succ (.param level)))
    let (type, value) ← lambdaTelescope info.value fun params body => do
      unless body.isAppOfArity ``Generator.create 3 do
        throwError "instrumentation: expected Generator.create, got {body}"
      let valueType := body.getAppArgs[0]!
      let sourceBody := (mkApp body.getAppArgs[2]! (mkConst ``Unit.unit)).headBeta
      withLocalDecl `m .implicit mType fun m => do
      withLocalDecl `instMonad .instImplicit (← mkAppM ``Monad #[m]) fun monad => do
      withLocalDecl `instCost .instImplicit (← mkAppM ``MonadCost #[m]) fun cost => do
      withLocalDecl `instLoop .instImplicit (← mkAppM ``ForIn #[m, mkConst ``Lean.Loop, mkConst ``Unit]) fun loop => do
      withLocalDeclD `yieldPrime (← mkArrow valueType (mkApp m (mkConst ``Unit))) fun yieldPrime => do
        let value ← translate { monad := m, yieldPrime := some yieldPrime } sourceBody
        let all := params ++ #[m, monad, cost, loop, yieldPrime]
        return (← mkForallFVars all (← inferType value), ← mkLambdaFVars all value)
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasMVar || value.hasMVar then throwError "instrumentation: unresolved metavariables"
    let decl := Declaration.defnDecl {
      name := dst, levelParams := info.levelParams ++ [level], type, value,
      hints := .regular 0, safety := .safe }
    addDecl decl (forceExpose := true)
    enableRealizationsForConst dst
    compileDecl decl
    modifyEnv (generatorExt.addEntry · (src, dst))

end Python.Cost.Instrumentation.Monadic
