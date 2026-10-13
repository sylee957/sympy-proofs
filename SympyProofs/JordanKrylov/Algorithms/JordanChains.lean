import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations

/-! # Algorithm 5: symbolic Jordan-chain assembly

The output contains lists of polynomial vectors, ordered from the highest-order
generalized eigenvector to the eigenvector. No roots need to be chosen.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Algorithm 5: precompute reduced powers and assemble all positive rank layers.
List traversal implements the paper's choice-and-removal loop in input order.
Each individual chain retains the paper's descending order. -/
def computeJordanChains (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ) : Finset (List (Fin n → K[X])) := Id.run do
  let powers := Vector.ofFn (fun k : Fin (ℓbar + 1) =>
    PolynomialOperations.reducedPower f k.val)
  let F := PolynomialOperations.applyMatrix f A
  let applyPower := fun k v =>
    PolynomialOperations.applyBivariateMatrix (powers[k]?.getD powers[0]) A v
  let mut chains := ∅
  for ℓ in (List.range ℓbar).reverse.map Nat.succ do
    for b in B ℓ do
      let mut chain := []
      let mut current := b
      for k in (List.range ℓ).reverse do
        chain := chain ++ [applyPower (k + 1) current]
        if 0 < k then
          current := F current
      chains := insert chain chains
  return chains

end SympyProofs.JordanKrylov
