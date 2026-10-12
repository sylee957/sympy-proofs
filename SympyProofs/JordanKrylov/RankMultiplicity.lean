import SympyProofs.JordanKrylov.JordanKrylovBasis
import SympyProofs.JordanKrylov.KrylovDecomposition

/-! # Uniqueness of positive Jordan–Krylov rank multiplicities

The dimension of the image under f(A)^k is deg(f) times the sum of
max(rank_f(b) - k, 0) over the basis generators b. Taking second differences
of these sums recovers the number of generators of every positive rank.
-/

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators DirectSum

/-- Polynomial powers act on a cyclic subspace by acting on its generator. -/
theorem map_krylovSpace_aeval_pow (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (k : ℕ) :
    (krylovSpace K A u).map ((aeval A f)^k).mulVecLin =
      krylovSpace K A ((aeval A f)^k *ᵥ u) := by
  unfold krylovSpace
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Matrix.mulVecLin_apply]
  have he (j : ℕ) : (aeval A f)^k *ᵥ krylovVector A u j =
      krylovVector A ((aeval A f)^k *ᵥ u) j := by
    simp only [krylovVector, Matrix.mulVec_mulVec]
    rw [((commute_aeval_pow K A f k).symm.pow_right j).eq]
  simp only [he]

/-- The dimension of a cyclic space after applying f(A)^k. -/
theorem finrank_map_krylovSpace (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar) (k : ℕ) :
    Module.finrank K ((krylovSpace K A u).map ((aeval A f)^k).mulVecLin) =
      (vectorRank K A f u - k) * f.natDegree := by
  rw [map_krylovSpace_aeval_pow]
  let r := vectorRank K A f u
  have hur : u ∈ powerKernel K A f r := mem_powerKernel_vectorRank K A f u hu
  by_cases hk : k < r
  · have hu0 : u ≠ 0 := by intro hz; simp [r, hz] at hk
    have hvker : (aeval A f)^k *ᵥ u ∈ powerKernel K A f r := by
      rw [mem_powerKernel, Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm,
        pow_add, ← Matrix.mulVec_mulVec]
      rw [(mem_powerKernel K A f r u).mp hur, Matrix.mulVec_zero]
    have hr := vectorRank_pow_mulVec K A f u hu0 hu rfl k hk
    have hv0 : (aeval A f)^k *ᵥ u ≠ 0 := by
      intro hz
      rw [hz, vectorRank_zero] at hr
      omega
    exact finrank_krylovSpace K A f hf hm _ hv0 hvker hr
  · have hz : (aeval A f)^k *ᵥ u = 0 :=
      (mem_powerKernel K A f k u).mp (powerKernel_le K A f (by omega) hur)
    rw [hz, krylovSpace_zero]
    simp [show vectorRank K A f u - k = 0 by dsimp [r] at hk; omega]

private theorem map_krylovSpace_le (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (k : ℕ) :
    (krylovSpace K A u).map ((aeval A f)^k).mulVecLin ≤ krylovSpace K A u := by
  rintro v ⟨w, hw, rfl⟩
  obtain ⟨q, rfl⟩ := (mem_krylovSpace_iff K A u w).mp hw
  apply (mem_krylovSpace_iff K A u _).mpr
  exact ⟨f^k * q, by simp [map_mul, map_pow, Matrix.mulVec_mulVec]⟩

/-- The image dimension is the sum of the contributions from the cyclic summands. -/
theorem IsJordanKrylovBasis.finrank_map (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B)
    [Fintype B] (k : ℕ) :
    Module.finrank K ((powerKernel K A f ℓbar).map ((aeval A f)^k).mulVecLin) =
      ∑ b : B, (vectorRank K A f b.val - k) * f.natDegree := by
  classical
  let V := fun b : B => (krylovSpace K A b.val).map ((aeval A f)^k).mulVecLin
  have hind : iSupIndep V := hB.2.2.mono (fun b => map_krylovSpace_le K A f b.val k)
  have hspan : (⨆ b : B, V b) =
      (powerKernel K A f ℓbar).map ((aeval A f)^k).mulVecLin := by
    rw [← Submodule.map_iSup]
    congr 1
    simpa only [iSup_subtype] using hB.1.symm
  let e : (⨁ b : B, V b) ≃ₗ[K]
      (powerKernel K A f ℓbar).map ((aeval A f)^k).mulVecLin :=
    (LinearEquiv.ofInjective (DirectSum.coeLinearMap V) hind.dfinsupp_lsum_injective).trans
      (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap.trans hspan))
  rw [← e.finrank_eq, Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro b _
  exact finrank_map_krylovSpace K A f hf hm b.val
    (IsKrylovGeneratingSet.subset K A _ B hB.1 b.property) k

private theorem rank_count_identity {ι : Type*} [Fintype ι] (ranks : ι → ℕ)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ i, (ranks i - (r - 1))) + (∑ i, (ranks i - (r + 1))) =
      2 * (∑ i, (ranks i - r)) + ∑ i, if ranks i = r then 1 else 0 := by
  classical
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

/-- Two bases have equal rank-tail sums, since they describe the same image dimensions. -/
theorem IsJordanKrylovBasis.rank_tail_sum_eq (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B C : Set (Fin n → K))
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B)
    (hC : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) C)
    [Fintype B] [Fintype C] (k : ℕ) :
    (∑ b : B, (vectorRank K A f b.val - k)) =
      ∑ c : C, (vectorRank K A f c.val - k) := by
  have h := (hB.finrank_map K A f hf hm B k).symm.trans (hC.finrank_map K A f hf hm C k)
  rw [← Finset.sum_mul, ← Finset.sum_mul] at h
  exact Nat.eq_of_mul_eq_mul_right hf.natDegree_pos h

private theorem ncard_rank_eq_sum (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (B : Set (Fin n → K)) [Fintype B] (r : ℕ) :
    {u ∈ B | vectorRank K A f u = r}.ncard =
      ∑ b : B, if vectorRank K A f b.val = r then 1 else 0 := by
  classical
  let e : {u // u ∈ B ∧ vectorRank K A f u = r} ≃
      {b : B // vectorRank K A f b.val = r} :=
    { toFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
      invFun := fun b => ⟨b.val.val, b.val.property, b.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card {u // u ∈ B ∧ vectorRank K A f u = r} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- The uniqueness part of Theorem 12: the numbers of generators of every
positive rank agree for all Jordan–Krylov bases of the primary power kernel. -/
theorem positiveRankCounts_unique (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (ℓbar : ℕ) :
    ∀ B C : Set (Fin n → K),
      IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B →
      IsJordanKrylovBasis K A (powerKernel K A f ℓbar) C →
      ∀ r : ℕ, 1 ≤ r →
        {u ∈ B | vectorRank K A f u = r}.ncard =
          {u ∈ C | vectorRank K A f u = r}.ncard := by
  classical
  intro B C hB hC r hr
  let : Fintype B := hB.2.1.fintype
  let : Fintype C := hC.2.1.fintype
  have h₀ := hB.rank_tail_sum_eq K A f hf hm B C hC (r - 1)
  have h₁ := hB.rank_tail_sum_eq K A f hf hm B C hC r
  have h₂ := hB.rank_tail_sum_eq K A f hf hm B C hC (r + 1)
  have hb := rank_count_identity (fun b : B => vectorRank K A f b.val) r hr
  have hc := rank_count_identity (fun c : C => vectorRank K A f c.val) r hr
  rw [ncard_rank_eq_sum, ncard_rank_eq_sum]
  omega

end SympyProofs.JordanKrylov
