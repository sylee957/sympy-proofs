import SympyProofs.JordanKrylov.Algorithms.Operations

/-! # Computing primary Krylov generators

Algorithm 1 in imperative form. The vector annihilating polynomials are inputs.
The algorithm runs over a field with decidable equality, using supplied
polynomial operations. Correctness is proved in `PrimaryGeneratingCorrectness`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1: compute the maximum multiplicity, process ranks in descending
order, and return their lists of cofactor vectors indexed by rank.
Unoccupied ranks, including zero, return an empty list.
Input order and repetitions are preserved within each layer. -/
def computePrimaryGenerators (K : Type*) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (p : Fin m → K[X]) :
    ℕ → List (Fin n → K) := Id.run do
  let ranks := Vector.ofFn (fun i => Operations.multiplicity f (p i))
  let maxRank := Finset.univ.sup (fun i : Fin m => ranks[i.val])
  let mut generators : ℕ → List (Fin n → K) := fun _ => []
  for k in (List.range maxRank).reverse do
    let ℓ := k + 1
    let mut layer := []
    for i in List.finRange m do
      if 0 < ℓ ∧ ranks[i.val] = ℓ then
        let divisor := Operations.pow f (ranks[i.val])
        let cofactor := Operations.divMonic divisor (p i)
        let vector := Operations.applyMatrix cofactor A (e i)
        layer := layer ++ [vector]
    generators := Function.update generators ℓ layer
  return generators

end SympyProofs.JordanKrylov
