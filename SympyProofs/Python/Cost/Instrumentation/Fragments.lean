module

public import SympyProofs.Python.Cost.Instrumentation.Monadic.Basic
public meta import Lean

/-!
# Extracting proof fragments from generated computations

These utilities select existing subexpressions or cut a computation at a control
boundary. They never invent arithmetic or cost events. A caller must prove that
its selected fragments recompose to the complete computation; extraction alone
does not certify that a boundary was chosen correctly.
-/

public meta section
open Lean Meta
namespace Python.Cost.Instrumentation.Fragments

abbrev Boundary := Expr → Bool

def contains (boundary : Boundary) (e : Expr) : Bool :=
  (e.find? boundary).isSome

/-- Visit the first matching expression, opening surrounding binders in its context. -/
partial def withFirst (boundary : Boundary) (e : Expr)
    (visit : Expr → MetaM Unit) : MetaM Unit := do
  let e := e.consumeMData
  if boundary e then return ← visit e
  match e with
  | .lam .. =>
    lambdaTelescope e fun _ body => withFirst boundary body visit
  | .letE name type value body _ =>
    if contains boundary value then
      withFirst boundary value visit
    else
      withLetDecl name type value fun x => withFirst boundary (body.instantiate1 x) visit
  | _ =>
    for arg in e.getAppArgs do
      if contains boundary arg then return ← withFirst boundary arg visit
    throwError "fragment extraction: control boundary not found"

/-- The latest variable of the requested type at the selected control boundary. -/
def latestValue (type : Expr) : MetaM Expr := do
  let mut found := none
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && (← isDefEq decl.type type) then
      found := some decl.toExpr
  let some value := found | throwError "fragment extraction: no current value of type {type}"
  return value

/-- Keep the executed prefix, returning its latest value of `resultType` at the boundary.
Bindings and both conditional branches are preserved. A boundary inside a bound
action ends the prefix inside that action, before the outer continuation. -/
partial def before (ctx : Monadic.Context) (resultType : Expr) (boundary : Boundary)
    (e : Expr) (current : Option Expr := none) : MetaM Expr := do
  let e := e.consumeMData
  if boundary e then
    let some value := current | throwError "fragment extraction: boundary has no result value"
    return ← Monadic.pureM ctx value
  let args := e.getAppArgs
  if e.isAppOfArity ``Bind.bind 6 then
    if contains boundary args[4]! then
      return ← before ctx resultType boundary args[4]! current
    return ← withLocalDeclD `value args[2]! fun x => do
      let current := if ← isDefEq args[2]! resultType then some x else current
      Monadic.bindM ctx args[4]! x
        (← before ctx resultType boundary (mkApp args[5]! x).headBeta current)
  if e.isAppOfArity ``ite 5 then
    let yes ← before ctx resultType boundary args[3]! current
    let no ← before ctx resultType boundary args[4]! current
    return ← mkAppOptM ``ite #[none, some args[1]!, some args[2]!, some yes, some no]
  throwError "fragment extraction: unsupported prefix shape {e.getAppFn}"

/-- Remove only terminal `ForInStep.yield` packaging; keep all executed actions.
A `done` return is rejected, so a break cannot silently become a normal update. -/
partial def yieldingValue (ctx : Monadic.Context) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let args := e.getAppArgs
  if e.isAppOfArity ``Pure.pure 4 then
    unless args[3]!.isAppOfArity ``ForInStep.yield 2 do
      throwError "fragment extraction: expected a yielding return"
    return ← Monadic.pureM ctx args[3]!.getAppArgs[1]!
  if e.isAppOfArity ``Bind.bind 6 then
    return ← withLocalDeclD `value args[2]! fun x => do
      Monadic.bindM ctx args[4]! x (← yieldingValue ctx (mkApp args[5]! x).headBeta)
  if e.isAppOfArity ``ite 5 then
    let yes ← yieldingValue ctx args[3]!
    let no ← yieldingValue ctx args[4]!
    return ← mkAppOptM ``ite #[none, some args[1]!, some args[2]!, some yes, some no]
  throwError "fragment extraction: unsupported return shape {e.getAppFn}"

/-- Close an extracted expression over explicit parameters and kernel-check its definition.
Unexpected captured variables cause an error rather than becoming implicit inputs. -/
def define (name : Name) (levels : List Name) (params : Array Expr) (body : Expr) : MetaM Unit := do
  let value ← instantiateMVars (← mkLambdaFVars params body)
  let type ← instantiateMVars (← mkForallFVars params (← inferType body))
  if value.hasFVar || type.hasFVar then
    throwError "fragment extraction: {name} captures an undeclared parameter"
  if value.hasMVar || type.hasMVar then
    throwError "fragment extraction: {name} has unresolved metavariables"
  let decl := Declaration.defnDecl {
    name, levelParams := levels, type, value, hints := .regular 0, safety := .safe }
  addDecl decl (forceExpose := true)
  enableRealizationsForConst name
  compileDecl decl

end Python.Cost.Instrumentation.Fragments
