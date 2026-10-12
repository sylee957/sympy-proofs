import SympyProofs.JordanKrylov.Mathematics.JordanChainRecurrence
import SympyProofs.JordanKrylov.Mathematics.EigenvectorPolynomial

/-!
# Exact orders of the generalized eigenvectors

Lemma 5 of the Jordan–Krylov paper: p^(k)(α,u) is killed by the k-th
power of A-αE, but not by its (k-1)-st power.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- Iterating the recurrence moves m steps down the chain. -/
theorem pChainAt_pow_mulVec (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) {ℓ k m : ℕ}
    (hm : m ≤ k) (hkℓ : k ≤ ℓ) :
    (A.map K.subtype - α • 1) ^ m *ᵥ pChainAt K A f ℓ k α u =
      pChainAt K A f ℓ (k - m) α u := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec,
      pChainAt_step K A f u α hα (by omega) hkℓ,
      ih (by omega) (by omega)]
    congr 1
    omega

/-- The first chain vector is the eigenvector polynomial applied to f(A)^(ℓ-1)u. -/
theorem pChainAt_one_eq_pAt (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    pChainAt K A f ℓ 1 α u = pAt K A f α (((aeval A f) ^ (ℓ - 1)) *ᵥ u) := by
  rw [pChainAt_eq_formula, pAt_eq_ψMatrix_mulVec]
  simp only [ψMatrix, bivariateMatrix_scalar, ψPower_specialize K f α hα, pow_one,
    RingHom.map_mulVec, Matrix.map_pow, Function.comp_def]

private theorem first_chain_vector_ne_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (hℓ : 1 ≤ ℓ)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    pChainAt K A f ℓ 1 α u ≠ 0 := by
  have hmem := (vectorRank_eq_iff K A f u hu hℓ).mp hrank
  have hw0 : ((aeval A f) ^ (ℓ - 1)) *ᵥ u ≠ 0 := hmem.2
  have hw : (aeval A f) *ᵥ (((aeval A f) ^ (ℓ - 1)) *ᵥ u) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', Nat.sub_add_cancel hℓ]
    exact hmem.1
  rw [pChainAt_one_eq_pAt K A f u ℓ α hα]
  exact pAt_ne_zero K A f hf _ hw0 hw α hα

/-- Lemma 5, nonvanishing: the (k-1)-st power does not kill p^(k)(α,u). -/
theorem pChainAt_pow_pred_ne_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) {k : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) :
    (A.map K.subtype - α • 1) ^ (k - 1) *ᵥ pChainAt K A f ℓ k α u ≠ 0 := by
  rw [pChainAt_pow_mulVec K A f u α hα (Nat.sub_le k 1) hkℓ]
  have hindex : k - (k - 1) = 1 := by omega
  rw [hindex]
  exact first_chain_vector_ne_zero K A f hf u hu hrank (by omega) α hα

/-- Lemma 5, annihilation: the k-th power kills p^(k)(α,u). -/
theorem pChainAt_pow_eq_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    {ℓbar : ℕ} (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) {k : ℕ} (hkℓ : k ≤ ℓ) :
    (A.map K.subtype - α • 1) ^ k *ᵥ pChainAt K A f ℓ k α u = 0 := by
  rw [pChainAt_pow_mulVec K A f u α hα le_rfl hkℓ, Nat.sub_self]
  exact pChainAt_zero_of_rank K A f u hu hrank α hα

end SympyProofs.JordanKrylov
