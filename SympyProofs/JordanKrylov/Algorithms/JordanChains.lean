import Init.Data.Range.Polymorphic
import SympyProofs.JordanKrylov.Algorithms.PolynomialOperations

/-! # Algorithm 5: symbolic Jordan-chain assembly

The output contains lists of polynomial vectors, ordered from the highest-order
generalized eigenvector to the eigenvector. No roots need to be chosen.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

private theorem powerTable_size {α : Type} (q : ℕ → α) (bound : ℕ) :
    (Id.run do
      let mut powers := #[q 0]
      for k in 1...=bound do
        powers := powers.push (q k)
      return powers).size = bound + 1 := by
  simp only [forIn, Std.Rcc.forIn'_eq_forIn'_toList]
  change (Id.run (forIn (1...=bound).toList #[q 0]
    (fun k out => pure (ForInStep.yield (out.push (q k)))))).size = _
  simp [List.forIn_pure_yield_eq_foldl]

private theorem descendingLayer_bounds {offset bound : ℕ} (h : offset < bound) :
    1 ≤ bound - offset ∧ bound - offset ≤ bound := by omega

private theorem powerTable_index_lt {size bound k : ℕ}
    (hsize : size = bound + 1) (hk : k ≤ bound) : k < size := by omega

/-- Algorithm 5: precompute reduced powers and assemble all positive rank layers.
List traversal implements the paper's choice-and-removal loop in input order.
Each individual chain retains the paper's descending order. -/
def computeJordanChains (K : Type) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : ℕ → List (Fin n → K)) (ℓbar : ℕ) : Finset (List (Fin n → K[X])) := Id.run do
  let zeroPower := PolynomialOperations.reducedPower f 0
  let powers := Id.run do
    let mut powers := #[zeroPower]
    for k in 1...=ℓbar do
      powers := powers.push (PolynomialOperations.reducedPower f k)
    return powers
  have powers_size : powers.size = ℓbar + 1 :=
    powerTable_size (PolynomialOperations.reducedPower f) ℓbar
  let F := PolynomialOperations.applyMatrix f A
  let mut chains := ∅
  for hOffset : offset in 0...ℓbar do
    let ℓ := ℓbar - offset
    have layer_bounds := descendingLayer_bounds hOffset.2
    for b in B ℓ do
      let mut chain := []
      let mut current := b
      -- Lines 6–9: compute exponents ℓ, …, 2, advancing after every entry.
      for step in 0...(ℓ - 1) do
        let k := ℓ - step
        have index_lt : k < powers.size :=
          powerTable_index_lt powers_size ((Nat.sub_le ℓ step).trans layer_bounds.2)
        chain := chain ++
          [PolynomialOperations.applyBivariateMatrix powers[k] A current]
        current := F current
      -- Line 10: finish with exponent 1, without another application of f(A).
      have one_lt : 1 < powers.size :=
        powerTable_index_lt powers_size (layer_bounds.1.trans layer_bounds.2)
      chain := chain ++ [PolynomialOperations.applyBivariateMatrix powers[1] A current]
      chains := insert chain chains
  return chains

end SympyProofs.JordanKrylov
