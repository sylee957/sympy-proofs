module

public import SympyProofs.LinearAlgebra.Permanent.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.Order.Preorder.Finite

/-! Permanents of triangular and block triangular matrices. -/

@[expose] public section

namespace Matrix

open Finset Equiv Equiv.Perm

/-- Only the identity permutation contributes to an upper triangular permanent. -/
theorem permanent_of_isUpperTriangular {n R : Type*} [CommSemiring R]
    [Fintype n] [LinearOrder n] {A : Matrix n n R} (hA : A.IsUpperTriangular) :
    A.permanent = ∏ i, A i i := by
  classical
  unfold permanent
  rw [sum_eq_single (1 : Perm n)]
  · simp
  · intro σ _ hσ
    have hmove : ∃ i, i < σ i := by
      by_contra h
      have hle : ∀ i, σ i ≤ i := fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
      apply hσ
      apply Equiv.ext
      intro i
      induction i using (wellFounded_lt (α := n)).induction with
      | h i ih =>
        rcases (hle i).lt_or_eq with hlt | heq
        · exact σ.injective (ih (σ i) hlt)
        · exact heq
    obtain ⟨i, hi⟩ := hmove
    exact prod_eq_zero (mem_univ i) (hA hi)
  · simp

/-- The lower triangular case follows by transposition. -/
theorem permanent_of_isLowerTriangular {n R : Type*} [CommSemiring R]
    [Fintype n] [LinearOrder n] {A : Matrix n n R} (hA : A.IsLowerTriangular) :
    A.permanent = ∏ i, A i i := by
  rw [← permanent_transpose A]
  exact permanent_of_isUpperTriangular (A := Aᵀ) (fun _ _ h => hA h)

/-- A zero lower-left block forces every contributing permutation to preserve the blocks. -/
@[simp]
theorem permanent_fromBlocks_zero₂₁ {m n R : Type*} [CommSemiring R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp only [permanent]
  let S := ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset
  calc
    _ = ∑ σ ∈ S, ∏ i, fromBlocks A B 0 D (σ i) i := by
      symm
      apply sum_subset (subset_univ S)
      intro σ _ hσ
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
        change σ ∉ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset at hσ
        rw [Set.mem_toFinset] at hσ
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index,
          forall_apply_eq_imp_iff] using mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσ
      obtain ⟨a, ha⟩ := not_forall.mp h1
      rcases hx : σ (Sum.inl a) with a' | b
      · exact False.elim (ha ⟨a', hx.symm⟩)
      · apply prod_eq_zero (mem_univ (Sum.inl a))
        simp [hx]
    _ = _ := by
      symm
      rw [sum_mul_sum, ← sum_product', univ_product_univ]
      apply sum_nbij (fun σ : Perm m × Perm n => σ.1.sumCongr σ.2)
      · intro σ _
        exact Set.mem_toFinset.mpr ⟨σ, rfl⟩
      · intro σ _ τ _ h
        have heq := DFunLike.congr_fun h
        apply Prod.ext
        · apply Equiv.ext
          intro i
          simpa only [Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] using heq (Sum.inl i)
        · apply Equiv.ext
          intro j
          simpa only [Perm.sumCongr_apply, Sum.map_inr, Sum.inr.injEq] using heq (Sum.inr j)
      · intro σ hσ
        change σ ∈ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset at hσ
        rw [Set.mem_toFinset] at hσ
        obtain ⟨τ, hτ⟩ := hσ
        exact ⟨τ, mem_univ _, hτ⟩
      · intro σ _
        simp [Fintype.prod_sum_type]

@[simp]
theorem permanent_fromBlocks_zero₁₂ {m n R : Type*} [CommSemiring R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← permanent_transpose, fromBlocks_transpose, transpose_zero,
    permanent_fromBlocks_zero₂₁, permanent_transpose, permanent_transpose]

end Matrix
