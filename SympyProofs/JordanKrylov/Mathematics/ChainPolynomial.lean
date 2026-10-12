import SympyProofs.JordanKrylov.Mathematics.Definition
import SympyProofs.JordanKrylov.Mathematics.VectorRank

/-!
# Definition 3: reduced powers and Jordan-chain polynomials

The outer variable of K[λ][μ] is μ. Reduction modulo f(λ) therefore
acts on each coefficient, which is itself a polynomial in λ.
The superscript k denotes a reduced power, not a derivative.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- ψ_f^(k): raise ψ_f to k, then reduce every μ-coefficient modulo f(λ).
As in the paper, f is assumed monic when using the remainder properties. -/
noncomputable def ψPower (K : Subfield ℂ) (f : K[X]) (k : ℕ) : Polynomial K[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff ((ψ K f ^ k).toFinsupp.coeff.mapRange
    (fun q => q %ₘ f) (by simp)))

/-- The coefficientwise remainder formula in Definition 3. -/
@[simp] theorem ψPower_coeff (K : Subfield ℂ) (f : K[X]) (k j : ℕ) :
    (ψPower K f k).coeff j = ((ψ K f) ^ k).coeff j %ₘ f := rfl

/-- Every coefficient of the reduced power has λ-degree below deg f. -/
theorem ψPower_coeff_degree_lt (K : Subfield ℂ) (f : K[X]) (hf : f.Monic)
    (k j : ℕ) : ((ψPower K f k).coeff j).degree < f.degree := by
  rw [ψPower_coeff]
  exact degree_modByMonic_lt _ hf

/-- Coordinate representation of ψ_f^(k)(A,λ E) f(A)^(ℓ-k) u.
The paper uses ℓ = rank_f(u) and 1 ≤ k ≤ ℓ; the expression is defined
without these hypotheses, which are needed for its Jordan-chain properties. -/
noncomputable def pChainCoordinates (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ k : ℕ) (u : Fin n → K) :
    Fin n → K[X] :=
  (ψPower K f k).eval₂ (Matrix.scalar (Fin n)) (A.map C) *ᵥ
    (fun i => C ((((aeval A f) ^ (ℓ - k)) *ᵥ u) i))

/-- p^(k)(λ,u), as one polynomial with vector coefficients over K. -/
noncomputable def pChain (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ k : ℕ) (u : Fin n → K) :
    PolynomialModule K (Fin n → K) :=
  PolynomialModule.ofCoordinates (pChainCoordinates K A f ℓ k u)

/-- Evaluate p^(k) at a complex value of λ. -/
noncomputable def pChainAt (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ k : ℕ) («λ» : ℂ)
    (u : Fin n → K) : Fin n → ℂ :=
  PolynomialModule.eval «λ»
    (PolynomialModule.map ℂ (PolynomialModule.mapVector ℂ) (pChain K A f ℓ k u))

/-- Formula (2): p^(k)(λ,u) = ψ_f^(k)(A,λ E) f(A)^(ℓ-k) u,
with the matrices and vector embedded into ℂ. -/
theorem pChainAt_eq_formula (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ k : ℕ) («λ» : ℂ)
    (u : Fin n → K) :
    pChainAt K A f ℓ k «λ» u =
      bivariateMatrix K (ψPower K f k) (A.map K.subtype) («λ» • 1) *ᵥ
        (((aeval A f).map K.subtype) ^ (ℓ - k) *ᵥ (fun i => K.subtype (u i))) := by
  have h := bivariate_mulVec_eval K A (ψPower K f k) «λ»
    (((aeval A f) ^ (ℓ - k)) *ᵥ u)
  have heval : pChainAt K A f ℓ k «λ» u =
      fun i => (pChainCoordinates K A f ℓ k u i).eval₂ K.subtype «λ» := by
    funext i
    exact PolynomialModule.eval_ofCoordinates ℂ (pChainCoordinates K A f ℓ k u) «λ» i
  rw [heval]
  simpa only [pChainCoordinates, RingHom.map_mulVec, Matrix.map_pow, Function.comp_def] using h

/-- Formula (2) with ℓ supplied by the rank from Definition 2. -/
theorem pChainAt_eq_formula_of_rank (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (k : ℕ) («λ» : ℂ) :
    pChainAt K A f ℓ k «λ» u =
      bivariateMatrix K (ψPower K f k) (A.map K.subtype) («λ» • 1) *ᵥ
        (((aeval A f).map K.subtype) ^ (ℓ - k) *ᵥ (fun i => K.subtype (u i))) := by
  simpa only [hrank] using
    pChainAt_eq_formula K A f (vectorRank K A f u) k «λ» u

end SympyProofs.JordanKrylov
