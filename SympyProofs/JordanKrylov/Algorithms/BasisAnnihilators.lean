import SympyProofs.JordanKrylov.Algorithms.Operations

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Compute minimal annihilators directly from grouped characteristic factors.
Push each exponent directly into its factor column: `multiplicities[j][i]`.
Once a vector is annihilated, append zero for its remaining factors. -/
def computeBasisAnnihilators (K : Type) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (factors : Array (K[X] × ℕ)) (e : Fin m → (Fin n → K)) :
    Array K[X] × Array (Array ℕ) := Id.run do
  let mut polynomials : Array K[X] := #[]
  let mut multiplicities : Array (Array ℕ) := Array.replicate factors.size #[]
  for i in List.finRange m do
    let mut b0 := e i
    let mut candidate := Operations.one
    let mut remaining := factors.toList
    for j in List.finRange factors.size do
      let (f, exponent) := factors[j.val]
      remaining := remaining.tail
      let mut used : ℕ := 0
      if b0 ≠ 0 then
        let mut cofactor := Operations.one
        for (g, multiplicity) in remaining do
          cofactor := Operations.mul cofactor (Operations.pow g multiplicity)
        let mut probe := if remaining.isEmpty then b0 else Operations.applyMatrix cofactor A b0
        for _ in List.range exponent do
          if probe = 0 then break
          probe := Operations.applyMatrix f A probe
          b0 := Operations.applyMatrix f A b0
          candidate := Operations.mul candidate f
          used := used + 1
      multiplicities := multiplicities.modify j.val (fun column => column.push used)
    polynomials := polynomials.push candidate
  return ⟨polynomials, multiplicities⟩

end SympyProofs.JordanKrylov
