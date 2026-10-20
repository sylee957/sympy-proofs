/-
Run with `lake env lean --run scripts/check_prime_exponent_costs.lean` after building
`SympyProofs.Binomial.Costs`. These are differential/trace regression checks,
supplementing the formal runtime theorem in `FullAsymptotics`.
-/
import SympyProofs.Binomial.Costs
import SympyProofs.Python.Int.Native
import SympyProofs.Python.ByteArray.Native

open PythonInt Python.Cost SympyBinomial.PrimeExponent

abbrev I := PythonInt.Native
abbrev B := PythonByteArray.Native

private def checkCase (n k : ℕ) : IO Unit := do
  let input : I := (n : I)
  let lower : I := (k : I)
  let expected : ℤ := n.choose k
  let pureResult := primeExponents I B input lower
  let traced := TraceT.run (primeExponentsM (m := TraceT Id) I B input lower)
  let costed := CostT.run (primeExponentsM (m := CostT Id) I B input lower) Models.schoolbook
  let offset := CostT.run (primeExponentsM (m := CostT Id) I B input lower) Models.schoolbook 37
  unless toInt pureResult = expected && toInt traced.1 = expected &&
      toInt costed.1 = expected && toInt offset.1 = expected do
    throw (IO.userError s!"value mismatch at ({n}, {k})")
  unless costed.2 = charge Models.schoolbook traced.2 && offset.2 = costed.2 + 37 do
    throw (IO.userError s!"trace/counter mismatch at ({n}, {k})")
  let budget := if k = 0 then 2 else 131072*(n+1)^2
  unless costed.2 ≤ budget do
    throw (IO.userError s!"budget exceeded at ({n}, {k}): {costed.2}")
  let count := CostT.run (primeExponentsM (m := CostT Id) I B input lower) Models.operations
  unless count.2 = traced.2.length do
    throw (IO.userError s!"operation count mismatch at ({n}, {k})")
  if k = 0 then
    unless traced.2.length = 1 && costed.2 = 2 do
      throw (IO.userError "early return evaluated the sieve")

private def checkBalanced : IO Unit := do
  for size in [0, 1, 31, 32, 33, 64, 129] do
    let factors := Array.replicate size (2 : I)
    for leaf in [1, 2, 32] do
      if hleaf : 0 < leaf then
        let traced := TraceT.run (balancedFactorsM (m := TraceT Id) I factors leaf hleaf)
        let costed := CostT.run (balancedFactorsM (m := CostT Id) I factors leaf hleaf)
          Models.schoolbook
        unless toInt costed.1 = (2 : ℤ)^size && toInt traced.1 = (2 : ℤ)^size &&
            costed.2 = charge Models.schoolbook traced.2 do
          throw (IO.userError s!"balanced product mismatch at size={size}, leaf={leaf}")

private def checkAll : IO Unit := do
  for n in [:65] do
    if n % 16 = 0 then
      IO.println s!"checking row {n}"
      (← IO.getStdout).flush
    for k in [:n+1] do
      checkCase n k
  for (n,k) in [(100,50), (200,100), (1000,500), (3000,1500), (1000000,0)] do
    IO.println s!"checking larger case ({n}, {k})"
    (← IO.getStdout).flush
    checkCase n k
    let costed := CostT.run (primeExponentsM (m := CostT Id) I B (n : I) (k : I))
      Models.schoolbook
    IO.println s!"n={n}, k={k}: schoolbook={costed.2}, result_bits={(toInt costed.1).natAbs.size}"
  checkBalanced
  IO.println "Passed 2150 complete-kernel cases and 21 balanced-product cases."

def main : IO Unit := checkAll

#print axioms SympyBinomial.PrimeExponent.factorBits_le_upper
#print axioms SympyBinomial.PrimeExponent.inputWidth_cube_le
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_isBigO
#print axioms SympyBinomial.PrimeExponent.balancedFactorsM_id

#print axioms SympyBinomial.PrimeExponent.balancedFactorsM_bounded
#print axioms SympyBinomial.PrimeExponent.quotientExponentM_bounded

#print axioms SympyBinomial.PrimeExponent.primeExponentsM_bounded
#print axioms SympyBinomial.ByteSieve.oddPrimesCostStream_budgeted
#print axioms SympyBinomial.ByteSieve.oddPrimesCostStream_forIn_erases
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_erases
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_run_eq_choose
#print axioms SympyBinomial.PrimeExponent.primeExponentsM_correct_bounded
