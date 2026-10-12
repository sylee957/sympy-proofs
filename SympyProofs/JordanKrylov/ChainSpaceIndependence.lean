import SympyProofs.JordanKrylov.ChainSpace
import SympyProofs.JordanKrylov.JordanKrylovBasis
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-! # Independence of chain spaces from distinct Krylov generators

Lemma 13 follows by extending an independent family of Krylov subspaces from
K to ℂ, then taking subspaces of those complexifications.
-/
namespace SympyProofs.JordanKrylov
open scoped BigOperators DirectSum

/-- Extension of scalars inside ℂⁿ preserves independence of K-subspaces. -/
theorem iSupIndep_complexSpan (K : Subfield ℂ) {n : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Submodule K (Fin n → K)) (hU : iSupIndep U) :
    iSupIndep (fun i => Submodule.span ℂ
      (complexVectorMap K n '' (U i : Set (Fin n → K)))) := by
  classical
  let b := fun i => Module.finBasis K (U i)
  let v := fun ij : Σ i, Fin (Module.finrank K (U i)) => (b ij.1 ij.2).val
  have hK : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc ij
    have hmem (i : ι) : (∑ j, c ⟨i, j⟩ • (b i j).val) ∈ U i := by
      apply Submodule.sum_mem
      intro j _
      exact (U i).smul_mem _ (b i j).property
    have hsum : (∑ i, ∑ j, c ⟨i, j⟩ • (b i j).val) = 0 := by
      simpa only [Fintype.sum_sigma, v] using hc
    have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero U).mp hU Finset.univ
      (fun i => ∑ j, c ⟨i, j⟩ • (b i j).val) (fun i _ => hmem i) hsum
      ij.1 (Finset.mem_univ _)
    have hz' : (∑ j, c ⟨ij.1, j⟩ • b ij.1 j) = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using hz
    exact Fintype.linearIndependent_iff.mp (b ij.1).linearIndependent
      (fun j => c ⟨ij.1, j⟩) hz' ij.2
  let g := fun ij => complexVectorMap K n (v ij)
  have hC : LinearIndependent ℂ g := by
    exact (linearIndependent_algebraMap_comp_iff (R := K) (S := ℂ)).mpr hK
  have hbound (i : ι) : Submodule.span ℂ (complexVectorMap K n '' (U i : Set _)) ≤
      Submodule.span ℂ (Set.range (fun j => g ⟨i, j⟩)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    have he := congrArg (fun y : U i => complexVectorMap K n y.val)
      ((b i).sum_repr ⟨x, hx⟩)
    have hmem : (∑ j, (b i).repr ⟨x, hx⟩ j • g ⟨i, j⟩) ∈
        Submodule.span ℂ (Set.range (fun j => g ⟨i, j⟩)) := by
      apply Submodule.sum_mem
      intro j _
      exact (Submodule.restrictScalars K
        (Submodule.span ℂ (Set.range (fun j => g ⟨i, j⟩)))).smul_mem _
          (Submodule.subset_span ⟨j, rfl⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at he
    exact he ▸ hmem
  intro i
  have hd : Disjoint {ij : Σ j, Fin (Module.finrank K (U j)) | ij.1 = i}
      {ij : Σ j, Fin (Module.finrank K (U j)) | ij.1 ≠ i} := by
    rw [Set.disjoint_left]
    exact fun _ h₁ h₂ => h₂ h₁
  apply (hC.disjoint_span_image hd).mono
  · apply (hbound i).trans
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl, rfl⟩
  · apply iSup_le
    intro j
    apply iSup_le
    intro hji
    apply (hbound j).trans
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, hji, rfl⟩

/-- Complexifying the Krylov spaces of independent generators preserves directness. -/
theorem IsJordanKrylovIndependent.complexKrylovSpaces (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (B : Set (Fin n → K))
    (hB : IsJordanKrylovIndependent K A B) :
    iSupIndep (fun b : B => complexKrylovSpace K A b.val) := by
  let : Fintype B := hB.1.fintype
  exact iSupIndep_complexSpan K (fun b : B => krylovSpace K A b.val) hB.2

/-- Lemma 13(1): the chain spaces from independent Krylov generators at a fixed
root satisfy the direct-sum condition. In fact containment proves this for any α. -/
theorem chainSpaces_independent_of_jordanKrylovIndependent (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K) (B : Set (Fin n → K))
    (hB : IsJordanKrylovIndependent K A B) (α : ℂ) :
    iSupIndep (fun b : B => chainSpace K A f b.val (vectorRank K A f b.val) α) := by
  apply (hB.complexKrylovSpaces K A B).mono
  intro b
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact pChainAt_mem_complexKrylovSpace K A f b.val _ _ α

/-- Lemma 13(2): the total chain spans from independent Krylov generators
satisfy the direct-sum condition. The spans are the images of P_A(b) in ℂⁿ. -/
theorem rootChainSpans_independent_of_jordanKrylovIndependent (K : Subfield ℂ) {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : Polynomial K) (B : Set (Fin n → K))
    (hB : IsJordanKrylovIndependent K A B) (α : Fin d → ℂ) :
    iSupIndep (fun b : B => rootChainSpan K A f b.val (vectorRank K A f b.val) α) :=
  (hB.complexKrylovSpaces K A B).mono
    (fun b => rootChainSpan_le_complexKrylovSpace K A f b.val _ α)

end SympyProofs.JordanKrylov
