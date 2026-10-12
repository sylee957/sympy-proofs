import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations

/-! # Computing primary Krylov generators

Algorithm 1 in imperative form. The vector annihilating polynomials are inputs.
The algorithm runs over a field with decidable equality, using supplied
polynomial operations. Correctness is proved in `PrimaryGeneratingCorrectness`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1: compute the maximum multiplicity, process ranks in descending
order, and return their lists of cofactor vectors indexed by rank.
The array has `maxRank + 1` entries, with an empty zero layer.
Input order and repetitions are preserved within each layer. -/
def computePrimaryGenerators (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (p : Fin m → K[X]) :
    Array (List (Fin n → K)) := Id.run do
  let ranks := Vector.ofFn (fun i => PolynomialOperations.multiplicity f (p i))
  let maxRank := Finset.univ.sup (fun i : Fin m => ranks[i.val])
  let mut generators : { a : Array (List (Fin n → K)) // a.size = maxRank + 1 } :=
    ⟨Array.replicate (maxRank + 1) [], by simp⟩
  for k in (List.finRange maxRank).reverse do
    let ℓ := k.val + 1
    let mut layer := []
    for i in List.finRange m do
      if 0 < ℓ ∧ ranks[i.val] = ℓ then
        let divisor := PolynomialOperations.pow f (ranks[i.val])
        let cofactor := PolynomialOperations.divMonic divisor (p i)
        let vector := PolynomialOperations.applyMatrix cofactor A (e i)
        layer := layer ++ [vector]
    generators := ⟨generators.val.set ℓ layer (by
      have := generators.property
      have := k.isLt
      omega), by simpa using generators.property⟩
  return generators.val

end SympyProofs.JordanKrylov
