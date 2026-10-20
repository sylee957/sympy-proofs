module

public import SympyProofs.Python.Cost.Instrumentation.Fragments

/-!
# Proof boundaries in the generated sieve

This command selects initialization, marking, and search from the generated
body. It contains no sieve arithmetic or event schedule. The selected definitions
are connected to the complete body by `oddPrimesBodyM_eq` in `Costs.ByteSieve`.
-/

public meta section
open Lean Meta Elab Command
open Python.Cost Python.Cost.Instrumentation
namespace SympyBinomial.ByteSieve

private def rangeLoop (e : Expr) : Bool :=
  e.isAppOfArity ``ForIn.forIn 8 && e.getAppArgs[1]! == mkConst ``Std.Legacy.Range

private def searchLoop (e : Expr) : Bool :=
  e.isAppOfArity ``ForIn.forIn 8 && e.getAppArgs[1]! == mkConst ``Lean.Loop

private def beforeRange (e : Expr) : Bool :=
  e.isAppOfArity ``Bind.bind 6 && Fragments.contains rangeLoop e.getAppArgs[4]!

private def sieveStop (e : Expr) : Bool :=
  e.isAppOfArity ``MonadCost.emit 3 &&
    e.getAppArgs[2]!.isAppOfArity ``Event.control 1 &&
    e.getAppArgs[2]!.appArg! == mkStrLit "sieve.stop"

/-- Select proof fragments from an instrumented generator, keeping its operations verbatim. -/
elab "extract_sieve_fragments " source:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let .defnInfo info ← getConstInfo src
    | throwError "fragment extraction requires a generated definition"
  unless info.safety == .safe do throwError "fragment extraction requires a safe definition"
  let mut registered := false
  for (_, target) in Monadic.generatorExt.getState (← getEnv) do
    if target == src then registered := true
  unless registered do throwError "fragment extraction requires a registered generated producer"
  let ns ← getCurrNamespace
  liftTermElabM do
    lambdaTelescope info.value fun ps body => do
      unless ps.size == 8 do throwError "fragment extraction: unexpected generator parameters"
      let carrier := ps[0]!
      let ctx : Monadic.Context := { monad := ps[3]! }
      let base := #[ps[0]!, ps[1]!, ps[3]!, ps[4]!, ps[5]!]
      let save (name : Name) (params : Array Expr) (value : Expr) : MetaM Unit := do
        Fragments.define (ns ++ name) info.levelParams params value
        addDocStringCore (ns ++ name)
          s!"Proof fragment extracted from `{src}`. See `oddPrimesBodyM_eq` and `sieveM_eq` for recomposition."
      save `initialM (base.push ps[2]!) (← Fragments.before ctx carrier beforeRange body)
      save `sieveM (base.push ps[2]!) (← Fragments.before ctx carrier sieveStop body)
      Fragments.withFirst rangeLoop body fun loop => do
        lambdaTelescope loop.getAppArgs[7]! fun inputs update => do
          unless inputs.size == 2 do throwError "fragment extraction: unexpected marking state"
          save `markM (base ++ inputs) (← Fragments.yieldingValue ctx update)
      -- Retain the complete while loop and its return, abstracting the saved table and index.
      Fragments.withFirst (fun e =>
          e.isAppOfArity ``Bind.bind 6 && searchLoop e.getAppArgs[4]!) body fun search => do
        let loop := search.getAppArgs[4]!
        let bytes ← Fragments.latestValue carrier
        let index := loop.getAppArgs[6]!
        unless index.isFVar do throwError "fragment extraction: expected a saved search index"
        save `searchM (base ++ #[ps[6]!, ps[7]!, bytes, index]) search
        lambdaTelescope loop.getAppArgs[7]! fun inputs step => do
          unless inputs.size == 2 do throwError "fragment extraction: unexpected search state"
          Fragments.withFirst (fun e =>
              e.isAppOfArity ``ite 5 && e.getAppArgs[0]!.getAppFn == ctx.monad) step fun branch => do
            let advance ← Fragments.yieldingValue ctx branch.getAppArgs[3]!
            save `advanceM (base ++ #[ps[7]!, bytes, inputs[1]!]) advance

end SympyBinomial.ByteSieve
