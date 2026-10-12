import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations

/-! # Computing primary Krylov generators

Algorithm 1 in imperative form. The vector annihilating polynomials are inputs.
The algorithm runs over a field with decidable equality, using supplied
polynomial operations. Correctness is proved in `PrimaryGeneratingCorrectness`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 1: compute the maximum multiplicity, process ranks in descending
order, and return the union of their cofactor vectors. The input indices are
visited in increasing order inside each layer. -/
def computePrimaryGenerators (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (e : Fin m → (Fin n → K)) (f : K[X]) (p : Fin m → K[X]) :
    Finset (Fin n → K) := Id.run do
  let ranks := fun i => PolynomialOperations.multiplicity f (p i)
  let maxRank := Finset.univ.sup ranks
  let mut generators := ∅
  for k in (List.range maxRank).reverse do
    let ℓ := k + 1
    let mut layer := ∅
    for i in List.finRange m do
      if 0 < ℓ ∧ ranks i = ℓ then
        let divisor := PolynomialOperations.pow f (ranks i)
        let cofactor := PolynomialOperations.divMonic divisor (p i)
        let vector := PolynomialOperations.applyMatrix cofactor A (e i)
        layer := insert vector layer
    generators := generators ∪ layer
  return generators

end SympyProofs.JordanKrylov
