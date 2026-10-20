module

public import SympyProofs.Python.Cost.Instrumentation.Primitives
public import SympyProofs.Python.Cost.Instrumentation.Loops
public import SympyProofs.Python.ByteArray
public meta import Lean

/-!
# Instrument an elaborated definition

`derive_costed source as target` reads the elaborated body of `source` and
generates `target`, with the same parameters and result `Checked (source …)`.
Notation and macros have already been resolved by Lean. The translator handles
registered arithmetic, lets, `Id` sequencing, branches, finite list loops and
calls to previously derived helpers. Unknown calls, recursion, and unsupported
control operators are errors.

For example, `derive_costed valuation as valuationInstrumented` leaves the
original definition unchanged. `(valuationInstrumented I n k).run` selects
`Id`, `TraceT` or `CostT` through its monad parameter. Its `run_id`, `run_cost`
and `cost_eq_trace` certificates apply to all inputs and charging policies.

The operation model treats literals, variable lookup, binding, static instance
dictionaries and literal closure creation as free. Arithmetic primitives and
comparisons produce events; list iteration records `for.next`.
No simplifier is run over the source: a let is evaluated once, and an unselected
branch is not evaluated. Only named interface aliases are unfolded.

The kernel checks the generated value certificate and the generic execution
and accounting theorems. The coverage audit is implemented by this metaprogram;
it is not a verified Lean compiler or a model of optimized machine code.
-/

public meta section

open Lean Meta Elab Command

namespace Python.Cost.Instrumentation

private def addDerived (s : NameMap Name) (e : Name × Name) : NameMap Name :=
  s.insert e.1 e.2

initialize derivedExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addDerived
    addImportedFn := mkStateFromImportedEntries addDerived {}
  }

private def checkedNS := ``Checked

private def checkedName (s : String) : Name := checkedNS ++ Name.mkSimple s

/-- Normalize only documented interface aliases, never arbitrary definitions. -/
partial def aliases (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``inferInstance 2 then
    aliases e.appArg!
  else if e.isAppOfArity ``PythonInt.Value 1 || e.isAppOfArity ``PythonByteArray.Value 1 then
    aliases e.appArg!
  else if e.isAppOfArity ``PythonInt.Value.bitCount 3 then
    mkAppN (mkConst ``PythonInt.bitCount) (e.getAppArgs.map aliases)
  else if e.isAppOfArity ``PythonInt.Value.bitLength 3 then
    mkAppN (mkConst ``PythonInt.bitLength) (e.getAppArgs.map aliases)
  else
    match e with
    | .app f a => .app (aliases f) (aliases a)
    | _ => e

private def sourceOf (checked : Expr) : MetaM Expr := do
  let t ← inferType checked
  unless t.isAppOfArity ``Checked 2 do
    throwError "instrumentation: invalid primitive contract {t}"
  return t.appArg!

/-- Ignore proof terms, which Lean erases, while retaining runtime structure. -/
partial def sameResolved (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if (← isProof a) && (← isProof b) then
    return ← isDefEq (← inferType a) (← inferType b)
  match a, b with
  | .app f x, .app g y => return (← sameResolved f g) && (← sameResolved x y)
  | _, _ => return false

/-- Exact resolved operation matching also checks the selected arithmetic instance.
Only proof terms may differ. Definitional equality of runtime terms is
deliberately insufficient for this coverage check. -/
def auditPrimitive (source result : Expr) : MetaM Unit := do
  let expected ← instantiateMVars (← sourceOf result)
  unless ← sameResolved (aliases source) (aliases expected) do
    throwError "instrumentation: resolved call {source.getAppFn} does not match \
      contract {result.getAppFn} (including its instances)"

private def pureValue (e : Expr) : MetaM Expr := mkAppM (checkedName "pure") #[e]

private def bindChecked (p : Expr) (x : Expr) (body : Expr) : MetaM Expr := do
  mkAppM (checkedName "bind") #[p, ← mkLambdaFVars #[x] body]

def primitive? (e : Expr) : MetaM (Option (Name × Nat)) := do
  let name := (e.getAppFn.constName?.getD .anonymous)
  let args := e.getAppArgs
  let (suffix, arity) ←
    if name == ``HAdd.hAdd then pure ("Add", 2)
    else if name == ``HSub.hSub then pure ("Sub", 2)
    else if name == ``HMul.hMul then pure ("Mul", 2)
    else if name == ``HDiv.hDiv then pure ("Div", 2)
    else if name == ``HMod.hMod then pure ("Mod", 2)
    else if name == ``HPow.hPow then pure ("Pow", 2)
    else if name == ``HAnd.hAnd then pure ("And", 2)
    else if name == ``HShiftLeft.hShiftLeft then pure ("Shl", 2)
    else if name == ``HShiftRight.hShiftRight then pure ("Shr", 2)
    else if name == ``Neg.neg then pure ("Neg", 1)
    else if name == ``BEq.beq then pure ("Eq", 2)
    else if name == ``bne then pure ("Ne", 2)
    else if name == ``PythonInt.bitCount then pure ("BitCount", 1)
    else if name == ``PythonInt.bitLength then pure ("BitLength", 1)
    else if name == ``Int.fdiv then return some (checkedName "intFdiv", 2)
    else if name == ``Nat.sqrt then return some (checkedName "natSqrt", 1)
    else if name == ``Bool.not then return some (checkedName "boolNot", 1)
    else if name == ``ForInStep.yield then return some (checkedName "stepYield", 1)
    else if name == ``ForInStep.done then return some (checkedName "stepDone", 1)
    else return none
  if args.size < arity then return none
  let ty ← inferType args[args.size - arity]!
  let ty := aliases ty
  let carrier :=
    if ty == mkConst ``Nat then "nat"
    else if ty == mkConst ``Int then "int"
    else "py"
  let contract := checkedName (carrier ++ suffix)
  if !(← getEnv).contains contract then return none
  return some (contract, arity)

mutual

partial def translate (original : Expr) : MetaM Expr := do
  let e := aliases original
  match e with
  | .fvar _ => pureValue e
  | .lit (.natVal _) => pureValue e
  | .proj structureName index value =>
    let p ← translate value
    withLocalDeclD `record (← inferType value) fun x => do
      bindChecked p x (← pureValue (.proj structureName index x))
  | .letE name type val body _ =>
    if (← whnf type).isForall then
      unless val.consumeMData.isLambda do
        throwError "instrumentation: computed function bindings need a contract"
      -- A local function (including an elaborator-generated join point) is
      -- expanded at its call sites; its runtime arguments are still bound once.
      translate (body.instantiate1 val)
    else
      let p ← translate val
      withLocalDeclD name type fun x => do
        bindChecked p x (← translate (body.instantiate1 x))
  | _ =>
    let args := e.getAppArgs
    if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
      let p ← translate args[2]!
      return ← withLocalDeclD `record (← inferType args[2]!) fun x => do
        bindChecked p x (← pureValue (mkAppN e.getAppFn (args.set! 2 x)))
    if e.isAppOf ``OfNat.ofNat then
      unless args.size == 3 do
        throwError "instrumentation: unsupported numeral instance in {original}"
      if args[0]! == mkConst ``Nat &&
          args[2]! == mkApp (mkConst ``instOfNatNat) args[1]! then
        return ← pureValue e
      let some n := args[1]!.rawNatLit?
        | throwError "instrumentation: only literal numerals are supported"
      let contract ←
        if args[0]! == mkConst ``Int then mkAppM (checkedName "intNumeral") #[args[1]!]
        else if n == 0 then mkAppOptM (checkedName "pyZero") #[some args[0]!, none]
        else if n == 1 then mkAppOptM (checkedName "pyOne") #[some args[0]!, none]
        else mkAppOptM (checkedName "pyNumeral") #[some args[0]!, none, some args[1]!, none]
      auditPrimitive e contract
      return contract
    if e == mkConst ``Bool.true || e == mkConst ``Bool.false ||
        e.isAppOfArity ``PUnit.unit 0 || e.isAppOfArity ``Unit.unit 0 then
      return ← pureValue e
    if e.isAppOfArity ``Id.run 2 then
      return ← translate args[1]!
    if e.isAppOfArity ``Pure.pure 4 then
      unless args[0]! == mkConst ``Id [0] do
        throwError "instrumentation: only Id source sequencing is supported"
      -- Use the compiled standard instance, not synthesis in the user's scope.
      auditPrimitive e (← mkAppM (checkedName "idPure") #[args[3]!])
      return ← translate args[3]!
    if e.isAppOfArity ``Bind.bind 6 then
      auditPrimitive e (← mkAppM (checkedName "idBind") #[args[4]!, args[5]!])
      let p ← translate args[4]!
      return ← withLocalDeclD `bound args[2]! fun x => do
        bindChecked p x (← translate (mkApp args[5]! x))
    if e.isAppOfArity ``ite 5 then
      let test ← translateDecision args[1]! args[2]!
      let yes ← translate args[3]!
      let no ← translate args[4]!
      return ← withLocalDeclD `unit (mkConst ``Unit) fun u => do
        return ← mkAppM (checkedName "branchProp")
          #[args[1]!, test, ← mkLambdaFVars #[u] yes, ← mkLambdaFVars #[u] no]
    if e.isAppOfArity ``ForIn.forIn 8 then
      unless args[0]! == mkConst ``Id [0] && args[1]!.isAppOfArity ``List 1 do
        throwError "instrumentation: this loop needs a supported iteration contract"
      let f := args[7]!
      let step ← lambdaTelescope f fun params body => do
        unless params.size == 2 do
          throwError "instrumentation: the loop body must expose two parameters"
        mkLambdaFVars params (← translate body)
      return ← translateOperands #[args[5]!, args[6]!] #[] fun xs => do
        let result ← mkAppM (checkedName "listForIn") #[xs[0]!, xs[1]!, f, step]
        auditPrimitive (mkAppN e.getAppFn ((args.set! 5 xs[0]!).set! 6 xs[1]!)) result
        return result
    if let .lam name type body _ := e.getAppFn then
      if args.isEmpty then
        throwError "instrumentation: unsupported function value"
      let p ← translate args[0]!
      return ← withLocalDeclD name type fun x => do
        let rest := mkAppN (body.instantiate1 x) (args.extract 1 args.size)
        bindChecked p x (← translate rest)
    if let some (contract, arity) ← primitive? e then
      let operands := args.extract (args.size - arity) args.size
      let head := mkAppN e.getAppFn (args.extract 0 (args.size - arity))
      return ← translateOperands operands #[] fun xs => do
        let result ← mkAppM contract xs
        auditPrimitive (mkAppN head xs) result
        return result
    if let some target := derivedExt.getState (← getEnv) |>.find? (e.getAppFn.constName?.getD .anonymous) then
      return ← translateCallArguments args #[] fun xs => do
        let result := mkAppN (mkConst target e.getAppFn.constLevels!) xs
        auditPrimitive (mkAppN e.getAppFn xs) result
        return result
    throwError "instrumentation: unsupported call or expression {original}\n\
      Add an explicit operation contract; unknown work is never charged as zero."

private partial def translateOperands (todo done : Array Expr)
    (finish : Array Expr → MetaM Expr) : MetaM Expr := do
  if todo.isEmpty then return ← finish done
  let e := todo[0]!
  let p ← translate e
  withLocalDeclD `arg (← inferType e) fun x => do
    let body ← translateOperands (todo.extract 1 todo.size) (done.push x) finish
    bindChecked p x body

private partial def translateCallArguments (todo done : Array Expr)
    (finish : Array Expr → MetaM Expr) : MetaM Expr := do
  if todo.isEmpty then return ← finish done
  let e := todo[0]!
  let type ← inferType e
  -- Type arguments, proofs and instance dictionaries are static parameters of
  -- this abstract operation model, not Python integer computations.
  if (← isProp type) || (← whnf type).isSort || (← isClass? type).isSome then
    return ← translateCallArguments (todo.extract 1 todo.size) (done.push e) finish
  let p ← translate e
  withLocalDeclD `arg type fun x => do
    bindChecked p x (← translateCallArguments (todo.extract 1 todo.size) (done.push x) finish)

partial def translateDecision (prop inst : Expr) : MetaM Expr := do
  let args := prop.getAppArgs
  if prop.isAppOfArity ``Eq 3 && args[0]! == mkConst ``Bool &&
      args[2]! == mkConst ``Bool.true then
    auditPrimitive (mkApp2 (mkConst ``decide) prop inst)
      (← mkAppM (checkedName "boolDecision") #[args[1]!])
    return ← translate args[1]!
  let name := (prop.getAppFn.constName?.getD .anonymous)
  if name != ``LT.lt && name != ``LE.le && name != ``Eq then
    throwError "instrumentation: unsupported condition {prop}"
  let operands := args.extract (args.size - 2) args.size
  let head := mkAppN prop.getAppFn (args.extract 0 (args.size - 2))
  let ty := aliases (← inferType operands[0]!)
  let carrier :=
    if ty == mkConst ``Nat then "nat" else if ty == mkConst ``Int then "int" else "py"
  let contract := checkedName (carrier ++
    if name == ``LT.lt then "Lt" else if name == ``LE.le then "Le" else "DecEq")
  -- Audit the original decision, including its Decidable instance, before
  -- introducing local values for operands.
  let original := mkApp2 (mkConst ``decide) prop inst
  let check ← mkAppM contract operands
  auditPrimitive original check
  translateOperands operands #[] fun xs => do
    let result ← mkAppM contract xs
    unless (← isDefEq (← sourceOf result)
        (← mkDecide (mkAppN head xs))) do
      throwError "instrumentation: inconsistent comparison contract"
    return result

end

/-- Generate a certified cost interpretation of an existing elaborated definition. -/
elab "derive_costed " source:ident " as " target:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let .defnInfo info ← getConstInfo src
    | throwErrorAt source "instrumentation requires a transparent definition"
  unless info.safety == .safe do
    throwErrorAt source "instrumentation requires a safe definition"
  let dst := (← getCurrNamespace) ++ target.getId
  liftTermElabM do
    let (type, value) ← lambdaTelescope info.value fun params body => do
      let checked ← translate body
      let expected ← mkAppM ``Checked #[mkAppN (mkConst src (info.levelParams.map mkLevelParam)) params]
      unless ← isDefEq (← inferType checked) expected do
        throwError "instrumentation: generated result does not match the source"
      return (← mkForallFVars params expected, ← mkLambdaFVars params checked)
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasMVar || value.hasMVar then
      throwError "instrumentation: unresolved metavariables"
    let decl := Declaration.defnDecl {
      name := dst, levelParams := info.levelParams, type, value,
      hints := .regular 0, safety := .safe
    }
    -- Export the body so downstream trace proofs can inspect generated events.
    addDecl decl (forceExpose := true)
    enableRealizationsForConst dst
    compileDecl decl
    modifyEnv (derivedExt.addEntry · (src, dst))

end Python.Cost.Instrumentation
