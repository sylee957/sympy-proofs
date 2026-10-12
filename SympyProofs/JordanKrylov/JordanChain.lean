import SympyProofs.JordanKrylov.GeneralizedEigenvectors

/-!
# Jordan chains from the chain polynomials

Theorem 6 of the Jordan–Krylov paper. The sequence is ordered as in the
paper: p^(ℓ), p^(ℓ-1), ..., p^(1), ending with an ordinary eigenvector.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- A Jordan chain of length ℓ, ordered from the highest-order generalized
eigenvector to the ordinary eigenvector. Applying T-αI advances one step;
applying it to the final vector gives zero. This definition works over any
field and does not require the vector space to be finite-dimensional. -/
def IsJordanChain {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ℓ : ℕ} (T : Module.End K V) (α : K) (v : Fin ℓ → V) : Prop :=
  0 < ℓ ∧ (∀ j, v j ≠ 0) ∧
    ∀ j : Fin ℓ, (T - α • 1) (v j) =
      if h : j.val + 1 < ℓ then v ⟨j.val + 1, h⟩ else 0

/-- Theorem 6: the displayed sequence p^(ℓ)(α,u), ..., p^(1)(α,u)
is a Jordan chain of length ℓ at each root α of f. -/
theorem pChainAt_isJordanChain (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu0 : u ≠ 0) {ℓbar : ℕ}
    (hu : u ∈ powerKernel K A f ℓbar) {ℓ : ℕ}
    (hrank : vectorRank K A f u = ℓ) (α : ℂ)
    (hα : f.eval₂ K.subtype α = 0) :
    IsJordanChain (A.map K.subtype).mulVecLin α
      (fun j : Fin ℓ => pChainAt K A f ℓ (ℓ - j.val) α u) := by
  have hℓ : 0 < ℓ := by
    have h := (vectorRank_bounds K A f u hu0 hu).1
    rw [hrank] at h
    omega
  refine ⟨hℓ, ?_, ?_⟩
  · intro j hz
    dsimp only at hz
    have h := pChainAt_pow_pred_ne_zero K A f hf u hu hrank α hα
      (by omega : 1 ≤ ℓ - j.val) (Nat.sub_le ℓ j.val)
    rw [hz, Matrix.mulVec_zero] at h
    exact h rfl
  · intro j
    have h := pChainAt_step K A f u α hα
      (by omega : 1 ≤ ℓ - j.val) (Nat.sub_le ℓ j.val)
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Matrix.mulVecLin_apply]
    split_ifs with hj
    · have he : ℓ - j.val - 1 = ℓ - (j.val + 1) := by omega
      simpa only [he] using h
    · have he : ℓ - j.val - 1 = 0 := by omega
      rw [he, pChainAt_zero_of_rank K A f u hu hrank α hα] at h
      exact h

end SympyProofs.JordanKrylov
