import SympyProofs.JordanKrylov.Mathematics.PrimaryGeneratingSet

/-! # Operations supplied to the primary generating algorithm

The operations are supplied as data; their mathematical specifications are separate proofs.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Polynomial operations used by Algorithm 1, without correctness proof inputs. -/
class PolynomialOperations (K : Type*) [Field K] where
  /-- `pow p k` computes the polynomial power `p ^ k`. -/
  pow : K[X] → ℕ → K[X]
  /-- Multiplicity of monic, positive-degree `f` in nonzero `p`. -/
  multiplicity : K[X] → K[X] → ℕ
  /-- `divMonic q p` returns `p /ₘ q` for monic `q`; divisor first. -/
  divMonic : K[X] → K[X] → K[X]
  /-- `applyMatrix p A u` computes `p(A)u`. -/
  applyMatrix : {n : ℕ} → K[X] → Matrix (Fin n) (Fin n) K → (Fin n → K) → (Fin n → K)

/-- Specifications required to prove Algorithm 1 correct. -/
structure PolynomialOperations.IsCorrect (K : Type*) [Field K]
    [PolynomialOperations K] : Prop where
  pow_eq : ∀ (p : K[X]) (k : ℕ), PolynomialOperations.pow p k = p ^ k
  multiplicity_eq : ∀ (f p : K[X]), 0 < f.natDegree → f.Monic → p ≠ 0 →
    PolynomialOperations.multiplicity f p = _root_.multiplicity f p
  divMonic_eq : ∀ (q p : K[X]), q.Monic → PolynomialOperations.divMonic q p = p /ₘ q
  applyMatrix_eq : ∀ {n} (p : K[X]) (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
    PolynomialOperations.applyMatrix p A u = aeval A p *ᵥ u

end SympyProofs.JordanKrylov
