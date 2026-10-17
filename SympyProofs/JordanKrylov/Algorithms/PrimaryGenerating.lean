import SympyProofs.JordanKrylov.Algorithms.Operations

/-! # Computing primary Krylov generators

Algorithm 1 in imperative form. The vector annihilating polynomials and their
exponents for the selected factor are inputs.
The algorithm runs over a field with decidable equality, using supplied
polynomial operations. Correctness is proved in `PrimaryGeneratingCorrectness`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1: consume the annihilator polynomials and the selected factor's
rank vector, returning primary rank layers together with their maximum rank.
The ranks come directly from the corresponding multiplicity column.
Input order and repetitions are preserved within each layer. -/
def computePrimaryGenerators (K : Type) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X])
    (polynomials : Vector K[X] m)
    (ranks : Vector ℕ m) :
    (ℕ → List (Fin n → K)) × ℕ := Id.run do
  let mut maxRank : ℕ := 0
  for i in List.finRange m do
    maxRank := max maxRank (ranks[i])
  let mut generators : ℕ → List (Fin n → K) := fun _ => []
  for k in (List.range maxRank).reverse do
    let ℓ := k + 1
    let mut layer := []
    for i in List.finRange m do
      let rank := ranks[i]
      if 0 < ℓ ∧ rank = ℓ then
        let divisor := Operations.pow f rank
        let cofactor := Operations.divMonic divisor polynomials[i]
        let vector := Operations.applyMatrix cofactor A (e i)
        layer := layer ++ [vector]
    generators := Function.update generators ℓ layer
  return (generators, maxRank)

end SympyProofs.JordanKrylov
