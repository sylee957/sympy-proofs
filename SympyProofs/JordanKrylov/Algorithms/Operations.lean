import SympyProofs.JordanKrylov.Mathematics.PrimaryGeneratingSet
import SympyProofs.JordanKrylov.Mathematics.ChainPolynomial

/-! # Backend operations supplied to the Jordan–Krylov algorithms

The operations are supplied as data; their mathematical specifications are separate proofs.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Arithmetic and characteristic-factorization operations used by the Jordan–Krylov algorithms. -/
class Operations (K : Type*) [Field K] where
  /-- Constant polynomial one. -/
  one : K[X]
  /-- Polynomial multiplication. -/
  mul : K[X] → K[X] → K[X]
  /-- `pow p k` computes the polynomial power `p ^ k`. -/
  pow : K[X] → ℕ → K[X]
  /-- `divMonic q p` returns `p /ₘ q` for monic `q`; divisor first. -/
  divMonic : K[X] → K[X] → K[X]
  /-- `applyMatrix p A u` computes `p(A)u`. -/
  applyMatrix : {n : ℕ} → K[X] → Matrix (Fin n) (Fin n) K → (Fin n → K) → (Fin n → K)
  /-- Compute the coefficientwise reduced power ψ_f^(k). -/
  reducedPower : K[X] → ℕ → Polynomial K[X]
  /-- Compute q(A, λ I)v as a vector of polynomials in λ. -/
  applyBivariateMatrix : {n : ℕ} → Polynomial K[X] → Matrix (Fin n) (Fin n) K →
    (Fin n → K) → (Fin n → K[X])

  /-- Factor the characteristic polynomial into distinct monic irreducibles. -/
  factorCharpoly : {n : ℕ} → Matrix (Fin n) (Fin n) K → Array (K[X] × ℕ)

/-- Mathematical specifications of the supplied backend operations. -/
structure Operations.IsCorrect (K : Type*) [Field K]
    [Operations K] : Prop where
  one_eq : Operations.one (K := K) = 1
  mul_eq : ∀ p q : K[X], Operations.mul p q = p * q
  pow_eq : ∀ (p : K[X]) (k : ℕ), Operations.pow p k = p ^ k
  divMonic_eq : ∀ (q p : K[X]), q.Monic → Operations.divMonic q p = p /ₘ q
  applyMatrix_eq : ∀ {n} (p : K[X]) (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
    Operations.applyMatrix p A u = aeval A p *ᵥ u
  reducedPower_coeff : ∀ (f : K[X]) (k j : ℕ),
    (Operations.reducedPower f k).coeff j =
      (((f.map C - C f) /ₘ (X - C (X : K[X]))) ^ k).coeff j %ₘ f
  applyBivariateMatrix_eq : ∀ {n} (q : Polynomial K[X]) (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K), Operations.applyBivariateMatrix q A v =
      q.eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ (fun i => C (v i))

  factorCharpoly_factors : ∀ {n} (A : Matrix (Fin n) (Fin n) K) (f m),
    (f, m) ∈ Operations.factorCharpoly A → f.Monic ∧ Irreducible f ∧ 0 < m
  factorCharpoly_distinct : ∀ {n} (A : Matrix (Fin n) (Fin n) K),
    ((Operations.factorCharpoly A).toList.map Prod.fst).Nodup
  factorCharpoly_product : ∀ {n} (A : Matrix (Fin n) (Fin n) K),
    A.charpoly = ((Operations.factorCharpoly A).toList.flatMap
      (fun fm => List.replicate fm.2 fm.1)).prod
  factorCharpoly_multiplicity : ∀ {n} (A : Matrix (Fin n) (Fin n) K) (f m),
    (f, m) ∈ Operations.factorCharpoly A → m = _root_.multiplicity f A.charpoly

/-- The reduced-power specification agrees with the paper's definition. -/
theorem Operations.IsCorrect.reducedPower_eq (K : Subfield ℂ)
    [Operations K] (hops : Operations.IsCorrect K) (f : K[X]) (k : ℕ) :
    Operations.reducedPower f k = ψPower K f k := by
  ext j : 1
  exact hops.reducedPower_coeff f k j

end SympyProofs.JordanKrylov
