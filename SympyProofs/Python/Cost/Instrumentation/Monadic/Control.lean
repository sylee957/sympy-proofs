module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public import SympyProofs.Python.Cost.Instrumentation.Storage
public meta import Lean

/-!
# Monadic sequencing and branching
-/

public meta section
open Lean Meta Elab Command
namespace Python.Cost.Instrumentation.Monadic

/-- Audit and translate a source condition, including byte truth tests. -/
def translateCondition (recur : Translator) (ctx : Context) (prop inst : Expr) : MetaM Expr := do
  let args := prop.getAppArgs
  let original := mkApp2 (mkConst ``decide) prop inst
  if prop.isAppOf ``LT.lt && args.back!.isAppOf ``PythonByteArray.Value.size then
    let bytes := args.back!.getAppArgs.back!
    auditPrimitive original (← mkAppM ``Checked.byteTruth #[bytes])
    return ← operands recur ctx #[bytes] #[] fun values => do
      runChecked ctx (← mkAppM ``Checked.byteTruth values)
  if prop.isAppOfArity ``Ne 3 then
    let (contract, values) ←
      if args[0]! == mkConst ``UInt8 then pure (``Checked.byteFlag, #[args[1]!])
      else if args[0]! == mkConst ``Int then pure (``Checked.signedNe, #[args[1]!, args[2]!])
      else throwError "instrumentation: unsupported inequality {prop}"
    auditPrimitive original (← mkAppM contract values)
    return ← operands recur ctx values #[] fun values => do
      runChecked ctx (← mkAppM contract values)
  runChecked ctx (← Instrumentation.translateDecision prop inst)

/-- Audit source `Pure` before translating its value. -/
def translatePure (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if args[0]!.isAppOfArity ``Generator.Computation 1 then
    let expected ← mkAppOptM ``Source.generatorPure
      #[some args[0]!.appArg!, some args[2]!, some args[3]!]
    unless ← sameResolved e (← unfoldDefinition expected) do
      throwError "instrumentation: unsupported generator Pure instance"
  else
    auditPrimitive e (← mkAppM ``Checked.idPure #[args[3]!])
  return ← recur ctx args[3]!

/-- Audit source sequencing and translate its continuation. -/
def translateBind (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if args[0]!.isAppOfArity ``Generator.Computation 1 then
    let expected ← mkAppOptM ``Source.generatorBind
      #[some args[0]!.appArg!, some args[2]!, some args[3]!, some args[4]!, some args[5]!]
    unless ← sameResolved e (← unfoldDefinition expected) do
      throwError "instrumentation: unsupported generator Bind instance"
  else
    auditPrimitive e (← mkAppM ``Checked.idBind #[args[4]!, args[5]!])
  let p ← recur ctx args[4]!
  return ← withLocalDeclD `bound args[2]! fun x => do
    bindM ctx p x (← recur ctx (mkApp args[5]! x))

/-- Translate a conditional without evaluating the unselected branch. -/
def translateBranch (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let prop := args[1]!
  let propArgs := prop.getAppArgs
  let p ←
    if prop.isAppOfArity ``Eq 3 && propArgs[0]! == mkConst ``Bool &&
        propArgs[2]! == mkConst ``Bool.true then do
      auditPrimitive (mkApp2 (mkConst ``decide) prop args[2]!)
        (← mkAppM ``Checked.boolDecision #[propArgs[1]!])
      recur ctx propArgs[1]!
    else
      translateCondition recur ctx prop args[2]!
  return ← withLocalDeclD `test (mkConst ``Bool) fun test => do
    let yes ← recur ctx args[3]!
    let no ← recur ctx args[4]!
    let prop ← mkEq test (mkConst ``Bool.true)
    let body ← mkAppOptM ``ite #[none, some prop, none, some yes, some no]
    bindM ctx p test body

/-- Record the test while retaining dependent branch proofs. -/
def translateDependentBranch (recur : Translator) (ctx : Context) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  let test ← runChecked ctx (← Instrumentation.translateDecision args[1]! args[2]!)
  let yes ← lambdaTelescope args[3]! fun ps body => do mkLambdaFVars ps (← recur ctx body)
  let no ← lambdaTelescope args[4]! fun ps body => do mkLambdaFVars ps (← recur ctx body)
  let branch ← mkAppOptM ``dite #[none, some args[1]!, some args[2]!, some yes, some no]
  return ← withLocalDeclD `ignored (mkConst ``Bool) fun x => bindM ctx test x branch

end Python.Cost.Instrumentation.Monadic
