module

public import SympyProofs.Python.Cost.Instrumentation.Primitives
public import SympyProofs.Python.ByteArray
public meta import Lean

/-! Shared checks on resolved operations. Recognition rules cannot bypass these checks. -/

public meta section
open Lean Meta
namespace Python.Cost.Instrumentation

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

def sourceOf (checked : Expr) : MetaM Expr := do
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

end Python.Cost.Instrumentation
