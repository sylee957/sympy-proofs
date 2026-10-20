module

public import SympyProofs.Python.Cost.Instrumentation.Fragments
public meta import SympyProofs.Python.Cost.Instrumentation.Derive

/-!
# Proof boundaries in the prime-exponent kernel

Select the prime consumer, quotient loop, and loop transition directly from the
original or generated kernel. No arithmetic or cost events are authored here.
The computation equalities in `Costs.PrimeExponent` check their recomposition.
-/

public meta section
open Lean Meta Elab Command
open Python.Cost Python.Cost.Instrumentation
namespace SympyBinomial.PrimeExponent

private def whileLoop (e : Expr) : Bool :=
  e.isAppOfArity ``ForIn.forIn 8 && e.getAppArgs[1]! == mkConst ``Lean.Loop

private def consumerLoop (e : Expr) : Bool :=
  e.isAppOfArity ``ForIn.forIn 8 && e.getAppArgs[1]! != mkConst ``Lean.Loop

/-- Read the operand of the source's nonzero test, without rebuilding the expression. -/
private def testedValue (test : Expr) : MetaM Expr := do
  unless test.isAppOfArity ``bne 4 do
    throwError "fragment extraction: expected a nonzero test, got {test}"
  return test.getAppArgs[2]!

/-- Cut the consumer immediately before its post-loop test, returning the tested value.
The preceding binds (including initialization and the whole loop) are retained. -/
private partial def quotientPrefix (ctx : Monadic.Context) (e : Expr) : MetaM Expr := do
  let e ← zetaReduce e
  let args := e.getAppArgs
  if e.isAppOfArity ``Bind.bind 6 then
    let action := args[4]!
    if action.isAppOfArity ``perform 6 then
      let value := action.getAppArgs[5]!
      if value.isAppOf ``bne then return ← Monadic.pureM ctx (← testedValue value)
    return ← withLocalDeclD `value args[2]! fun x => do
      Monadic.bindM ctx action x (← quotientPrefix ctx (mkApp args[5]! x).headBeta)
  if e.isAppOfArity ``ite 5 then
    let prop := args[1]!
    unless prop.isAppOfArity ``Eq 3 do
      throwError "fragment extraction: expected a Boolean branch"
    return ← Monadic.pureM ctx (← testedValue prop.getAppArgs[1]!)
  throwError "fragment extraction: quotient boundary not found in {e.getAppFn}"

/-- Extract shared proof fragments, requiring a registered target for costed extraction. -/
elab "extract_prime_fragments " source:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let .defnInfo info ← getConstInfo src
    | throwError "fragment extraction requires a transparent definition"
  unless info.safety == .safe do throwError "fragment extraction requires a safe definition"
  let ns ← getCurrNamespace
  liftTermElabM do
    lambdaTelescope info.value fun ps body => do
      let costed := ps.size == 9
      unless ps.size == 6 || costed do
        throwError "fragment extraction: unexpected kernel parameters"
      if costed then
        let mut registered := false
        for (_, entry) in Monadic.monadicExt.getState (← getEnv) do
          if entry.target == src then registered := true
        unless registered do throwError "fragment extraction requires a registered generated kernel"
      let ctx : Monadic.Context := { monad := if costed then ps[6]! else mkConst ``Id [0] }
      let base := #[ps[0]!, ps[2]!]
      let monadParams := if costed then ps.extract 6 9 else #[]
      let save (name : Name) (params : Array Expr) (value : Expr) : MetaM Unit := do
        let value ← if costed then pure value else mkAppM ``Id.run #[value]
        Fragments.define (ns ++ name) info.levelParams params value
        addDocStringCore (ns ++ name) s!"Proof fragment extracted from `{src}`."
      Fragments.withFirst consumerLoop body fun loop => do
        lambdaTelescope loop.getAppArgs[7]! fun inputs update => do
          unless inputs.size == 2 do throwError "fragment extraction: unexpected consumer state"
          let update ← zetaReduce update
          save (if costed then `primeFactorM else `factorCode)
            (base ++ #[ps[4]!, ps[5]!] ++ inputs ++ monadParams)
            (← Fragments.yieldingValue ctx update)
          let quotientBody ← if costed then do
            unless update.isAppOfArity ``Bind.bind 6 &&
                update.getAppArgs[4]!.isAppOfArity ``MonadCost.emit 3 do
              throwError "fragment extraction: expected the generated iteration event"
            pure (mkApp update.getAppArgs[5]! (mkConst ``Unit.unit)).headBeta
          else pure update
          let some cast := quotientBody.find? (fun e =>
              e.isAppOf ``Nat.cast && e.getAppArgs.back! == inputs[0]!)
            | throwError "fragment extraction: prime cast not found"
          withLocalDeclD `p (← inferType cast) fun p => do
            let quotientBody := quotientBody.replace fun e => if e == cast then some p else none
            save (if costed then `quotientExponentM else `quotientCode)
              (base ++ #[ps[4]!, ps[5]!, p] ++ monadParams)
              (← quotientPrefix ctx quotientBody)
            Fragments.withFirst whileLoop quotientBody fun inner => do
              lambdaTelescope inner.getAppArgs[7]! fun state step => do
                unless state.size == 2 do throwError "fragment extraction: unexpected quotient state"
                save (if costed then `quotientStepM else `quotientStep)
                  (base ++ #[p, state[1]!] ++ monadParams) (← zetaReduce step)

end SympyBinomial.PrimeExponent
