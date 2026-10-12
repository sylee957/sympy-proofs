import SympyProofs.JordanKrylov.Mathematics.Vec
import SympyProofs.JordanKrylov.Mathematics.PrimaryGeneratingSet

/-! # Operations supplied to the primary generating algorithm

The operations are supplied as data; their mathematical specifications are separate proofs.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Polynomial operations used by Algorithm 1, without correctness proof inputs. -/
class PolynomialOperations (K : Type*) [Field K] where
  pow : K[X] → ℕ → K[X]
  multiplicity : K[X] → K[X] → ℕ
  /-- Arguments are the divisor followed by the dividend. -/
  divMonic : K[X] → K[X] → K[X]
  applyMatrix : {n : ℕ} → K[X] → Matrix (Fin n) (Fin n) K → (Vec K n) → (Vec K n)

/-- Specifications required to prove Algorithm 1 correct. -/
structure PolynomialOperations.IsCorrect {K : Type*} [Field K]
    [PolynomialOperations K] : Prop where
  pow_eq : ∀ (p : K[X]) (k : ℕ), PolynomialOperations.pow p k = p ^ k
  multiplicity_eq : ∀ (f p : K[X]), 0 < f.natDegree → f.Monic → p ≠ 0 →
    PolynomialOperations.multiplicity f p = _root_.multiplicity f p
  divMonic_eq : ∀ (q p : K[X]), q.Monic → PolynomialOperations.divMonic q p = p /ₘ q
  applyMatrix_eq : ∀ {n} (p : K[X]) (A : Matrix (Fin n) (Fin n) K) (u : Vec K n),
    PolynomialOperations.applyMatrix p A u = aeval A p *ᵥ u

end SympyProofs.JordanKrylov
