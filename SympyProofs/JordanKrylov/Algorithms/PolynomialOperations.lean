import SympyProofs.JordanKrylov.Mathematics.PrimaryGeneratingSet
import SympyProofs.JordanKrylov.Mathematics.ChainPolynomial

/-! # Polynomial operations supplied to the Jordan–Krylov algorithms

The operations are supplied as data; their mathematical specifications are separate proofs.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Polynomial operations used by the Jordan–Krylov algorithms. -/
class PolynomialOperations (K : Type*) [Field K] where
  /-- `pow p k` computes the polynomial power `p ^ k`. -/
  pow : K[X] → ℕ → K[X]
  /-- Multiplicity of monic, positive-degree `f` in nonzero `p`. -/
  multiplicity : K[X] → K[X] → ℕ
  /-- `divMonic q p` returns `p /ₘ q` for monic `q`; divisor first. -/
  divMonic : K[X] → K[X] → K[X]
  /-- `applyMatrix p A u` computes `p(A)u`. -/
  applyMatrix : {n : ℕ} → K[X] → Matrix (Fin n) (Fin n) K → (Fin n → K) → (Fin n → K)
  /-- Compute the coefficientwise reduced power ψ_f^(k). -/
  reducedPower : K[X] → ℕ → Polynomial K[X]
  /-- Compute q(A, λ I)v as a vector of polynomials in λ. -/
  applyBivariateMatrix : {n : ℕ} → Polynomial K[X] → Matrix (Fin n) (Fin n) K →
    (Fin n → K) → (Fin n → K[X])

/-- Mathematical specifications of the supplied polynomial operations. -/
structure PolynomialOperations.IsCorrect (K : Type*) [Field K]
    [PolynomialOperations K] : Prop where
  pow_eq : ∀ (p : K[X]) (k : ℕ), PolynomialOperations.pow p k = p ^ k
  multiplicity_eq : ∀ (f p : K[X]), 0 < f.natDegree → f.Monic → p ≠ 0 →
    PolynomialOperations.multiplicity f p = _root_.multiplicity f p
  divMonic_eq : ∀ (q p : K[X]), q.Monic → PolynomialOperations.divMonic q p = p /ₘ q
  applyMatrix_eq : ∀ {n} (p : K[X]) (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
    PolynomialOperations.applyMatrix p A u = aeval A p *ᵥ u
  reducedPower_coeff : ∀ (f : K[X]) (k j : ℕ),
    (PolynomialOperations.reducedPower f k).coeff j =
      (((f.map C - C f) /ₘ (X - C (X : K[X]))) ^ k).coeff j %ₘ f
  applyBivariateMatrix_eq : ∀ {n} (q : Polynomial K[X]) (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K), PolynomialOperations.applyBivariateMatrix q A v =
      q.eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ (fun i => C (v i))

/-- The reduced-power specification agrees with the paper's definition. -/
theorem PolynomialOperations.IsCorrect.reducedPower_eq (K : Subfield ℂ)
    [PolynomialOperations K] (hops : PolynomialOperations.IsCorrect K) (f : K[X]) (k : ℕ) :
    PolynomialOperations.reducedPower f k = ψPower K f k := by
  ext j : 1
  exact hops.reducedPower_coeff f k j

end SympyProofs.JordanKrylov
