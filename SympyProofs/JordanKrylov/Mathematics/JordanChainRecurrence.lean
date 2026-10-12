import SympyProofs.JordanKrylov.Mathematics.ChainPolynomial

/-! # The recurrence for Jordan-chain polynomials -/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

private theorem scalar_eq_smul_one {n : ℕ} (α : ℂ) :
    Matrix.scalar (Fin n) α = α • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, h]

/-- Substituting a scalar matrix for λ is scalar specialization followed by matrix evaluation. -/
theorem bivariateMatrix_scalar (K : Subfield ℂ) {n : ℕ}
    (q : Polynomial K[X]) (B : Matrix (Fin n) (Fin n) ℂ) (α : ℂ) :
    bivariateMatrix K q B (α • 1) = aeval B (q.map (eval₂RingHom K.subtype α)) := by
  have hc : eval₂RingHom' ((Matrix.scalar (Fin n)).comp K.subtype) (α • 1)
      (fun a => Matrix.scalar_commute (K.subtype a) (fun _ => Commute.all _ _) (α • 1)) =
      (Matrix.scalar (Fin n)).comp (eval₂RingHom K.subtype α) := by
    apply RingHom.ext
    intro r
    change r.eval₂ ((Matrix.scalar (Fin n)).comp K.subtype) (α • 1) =
      Matrix.scalar (Fin n) (r.eval₂ K.subtype α)
    rw [← scalar_eq_smul_one]
    exact (Polynomial.hom_eval₂ r K.subtype (Matrix.scalar (Fin n)) α).symm
  unfold bivariateMatrix
  rw [hc, aeval_def, eval₂_map]
  rfl

/-- Reduction modulo f(λ) leaves evaluation at a root α unchanged. -/
theorem ψPower_specialize (K : Subfield ℂ) (f : K[X]) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) (k : ℕ) :
    (ψPower K f k).map (eval₂RingHom K.subtype α) =
      ((ψ K f).map (eval₂RingHom K.subtype α)) ^ k := by
  rw [← Polynomial.map_pow]
  ext j
  simp only [coeff_map, ψPower_coeff, coe_eval₂RingHom]
  exact eval₂_modByMonic_eq_self_of_root hα

private theorem ψ_specialize_identity (K : Subfield ℂ) (f : K[X]) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) :
    (X - C α) * (ψ K f).map (eval₂RingHom K.subtype α) = f.map K.subtype := by
  have h := congrArg (Polynomial.map (eval₂RingHom K.subtype α)) (ψ_identity K f)
  have hC : (eval₂RingHom K.subtype α).comp C = K.subtype := by
    ext a
    simp
  simpa [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_map,
    hC, hα] using h

private theorem map_aeval_complex (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    (aeval A f).map K.subtype = aeval (A.map K.subtype) (f.map K.subtype) := by
  refine map_aeval_eq_aeval_map (φ := K.subtype)
    (ψ := (K.subtype.mapMatrix : Matrix (Fin n) (Fin n) K →+*
      Matrix (Fin n) (Fin n) ℂ)) ?_ f A
  ext x i j
  by_cases h : i = j <;>
    simp [algebraMap, Matrix.scalar, Matrix.diagonal, Matrix.map_apply, h]

/-- The matrix identity used in the proof of Lemma 4. -/
theorem ψPower_matrix_step (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) {k : ℕ} (hk : 1 ≤ k) :
    (A.map K.subtype - α • 1) *
      bivariateMatrix K (ψPower K f k) (A.map K.subtype) (α • 1) =
      bivariateMatrix K (ψPower K f (k - 1)) (A.map K.subtype) (α • 1) *
        (aeval A f).map K.subtype := by
  let g := (ψ K f).map (eval₂RingHom K.subtype α)
  have hpoly : (X - C α) * g ^ k = g ^ (k - 1) * f.map K.subtype := by
    rw [← ψ_specialize_identity K f α hα]
    change (X - C α) * g ^ k = g ^ (k - 1) * ((X - C α) * g)
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    ring
  have h := congrArg (aeval (A.map K.subtype)) hpoly
  simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  simpa only [bivariateMatrix_scalar, ψPower_specialize K f α hα,
    map_pow, map_aeval_complex, g] using h

/-- The recurrence holds for every u when 1 ≤ k ≤ ℓ and f(α) = 0. -/
theorem pChainAt_step (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) {ℓ k : ℕ}
    (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) :
    (A.map K.subtype - α • 1) *ᵥ pChainAt K A f ℓ k α u =
      pChainAt K A f ℓ (k - 1) α u := by
  have hexp : ℓ - k + 1 = ℓ - (k - 1) := by omega
  rw [pChainAt_eq_formula, pChainAt_eq_formula]
  simp only [Matrix.mulVec_mulVec]
  rw [← mul_assoc, ψPower_matrix_step K A f α hα hk, mul_assoc, ← pow_succ', hexp]

/-- Lemma 4, with rank_f(u) = ℓ as an explicit precondition. -/
theorem pChainAt_step_of_rank (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) {k : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) :
    (A.map K.subtype - α • 1) *ᵥ pChainAt K A f ℓ k α u =
      pChainAt K A f ℓ (k - 1) α u := by
  subst ℓ
  exact pChainAt_step K A f u α hα hk hkℓ

/-- At rank ℓ, the extension of Definition 3 to k = 0 evaluates to zero.
Thus the k = 1 case of Lemma 4 is the ordinary eigenvector equation. -/
theorem pChainAt_zero_of_rank (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) :
    pChainAt K A f ℓ 0 α u = 0 := by
  have hker : ((aeval A f) ^ ℓ) *ᵥ u = 0 := by
    have h := mem_powerKernel_vectorRank K A f u hu
    rwa [hrank, mem_powerKernel] at h
  rw [pChainAt_eq_formula, bivariateMatrix_scalar, ψPower_specialize K f α hα,
    pow_zero, map_one, Matrix.one_mulVec, Nat.sub_zero]
  funext i
  have h := congrArg (fun v : Fin n → K => K.subtype (v i)) hker
  simpa only [RingHom.map_mulVec, Matrix.map_pow, Function.comp_def, Pi.zero_apply,
    map_zero] using h

end SympyProofs.JordanKrylov
