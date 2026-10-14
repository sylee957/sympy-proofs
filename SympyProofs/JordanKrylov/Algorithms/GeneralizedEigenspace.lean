import SympyProofs.JordanKrylov.Algorithms.PrimaryGenerating
import SympyProofs.JordanKrylov.Algorithms.RefinedJordanKrylovBasis
import SympyProofs.JordanKrylov.Algorithms.JordanChains

/-! # Algorithm 6: assembly of symbolic generalized eigenvectors

Compose Algorithms 1, 3, and 5. The supplied minimal annihilating polynomials
determine the maximum rank; `m` is the multiplicity in the characteristic
polynomial. Applying `f(A)` uses `PolynomialOperations.applyMatrix` in the
component algorithms, rather than materializing a separate matrix here.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Algorithm 6. The output encodes chains for every root of `f` symbolically;
evaluating a chain at a root gives its generalized eigenvectors. -/
def computeGeneralizedEigenspace (K : Type) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (e : Fin s → (Fin n → K)) (p : Fin s → K[X])
    (m : ℕ) (preprocess : Bool := false) : Finset (List (Fin n → K[X])) := Id.run do
  let ℓbar := Finset.univ.sup (fun i => PolynomialOperations.multiplicity f (p i))
  -- Line 2: primary Krylov generators, grouped by rank.
  let V := computePrimaryGenerators K A e f p
  -- Line 3: a Jordan–Krylov basis with the same rank-layer interface.
  let B := computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess
  -- Lines 4–5: assemble and return the symbolic Jordan chains.
  return computeJordanChains K A f B ℓbar

end SympyProofs.JordanKrylov
