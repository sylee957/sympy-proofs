import SympyProofs.JordanKrylov.Mathematics.PrimaryKernelDimension

/-! # Rank sums and the stopping criterion for Algorithm 3

For a basis of the full primary kernel, the sum of generator ranks equals the
characteristic multiplicity. An independent family attaining this sum already
spans the primary kernel, so no further candidates need to be processed.
-/

namespace SympyProofs.JordanKrylov
open Matrix Polynomial
open scoped DirectSum

/-- The dimension of an independent sum of primary Krylov spaces. -/
theorem IsJordanKrylovIndependent.finrank_sum
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) [Fintype B] (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K))) :
    Module.finrank K ↥(⨆ b : B, krylovSpace K A b.val) =
      (∑ b : B, vectorRank K A f b.val) * f.natDegree := by
  classical
  let e := (LinearEquiv.ofInjective (DirectSum.coeLinearMap
    (fun b : B => krylovSpace K A b.val)) hB.2.dfinsupp_lsum_injective).trans
    (LinearEquiv.ofEq _ _ DirectSum.range_coeLinearMap)
  rw [← e.finrank_eq, Module.finrank_directSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hz : b.val = 0
  · simp [hz]
  · exact finrank_krylovSpace K A f hf hm b.val hz (hker b.property) rfl

/-- Algorithm 3 may stop when the accepted independent generators' ranks sum
to the characteristic multiplicity. No assumption of generation is needed. -/
theorem IsJordanKrylovIndependent.isBasis_of_sum_ranks_eq
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) [Fintype B] (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (hsum : (∑ b : B, vectorRank K A f b.val) = multiplicity f A.charpoly) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B := by
  have heq : (⨆ b : B, krylovSpace K A b.val) = powerKernel K A f ℓbar := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact iSup_le fun b => krylovSpace_le_powerKernel K A f b.val ℓbar (hker b.property)
    · rw [hB.finrank_sum K A f hf hm B hker, hsum]
      exact finrank_powerKernel_le_charpoly_multiplicity K A f hf hm ℓbar
  refine ⟨?_, hB⟩
  simpa only [IsKrylovGeneratingSet, iSup_subtype] using heq.symm

/-- Equation (11), summed over generators: a basis of the full primary kernel
has total rank equal to the multiplicity of f in the characteristic polynomial. -/
theorem IsJordanKrylovBasis.sum_ranks_eq_charpoly_multiplicity
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (hfull : powerKernel K A f n ≤ powerKernel K A f ℓbar)
    (B : Set (Fin n → K)) [Fintype B]
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B) :
    (∑ b : B, vectorRank K A f b.val) = multiplicity f A.charpoly := by
  classical
  obtain ⟨α, hα⟩ := Complex.exists_root (f := f.map K.subtype) (by
    rw [Polynomial.degree_map]
    exact degree_pos_of_irreducible hf)
  have hroot : f.eval₂ K.subtype α = 0 := by simpa only [IsRoot, eval_map] using hα
  obtain ⟨e⟩ := basis_chainDirectSum_equiv_maxGenEigenspace K A f hf hm hfull B hB α hroot
  have hdim := e.finrank_eq
  rw [Module.finrank_directSum, LinearMap.finrank_maxGenEigenspace_eq,
    Matrix.charpoly_mulVecLin, Matrix.charpoly_map,
    rootMultiplicity_map_eq_multiplicity K f A.charpoly hf hm
      A.charpoly_monic.ne_zero α hroot] at hdim
  convert hdim using 1
  apply Finset.sum_congr rfl
  intro b _
  exact (finrank_chainSpace K A f hf b.val (hB.1.subset K A _ B b.property)
    rfl α hroot).symm

/-- Grouping generator ranks by their positive rank subsets.
Zero generators contribute zero and need not be excluded. -/
theorem sum_ranks_eq_sum_rankCounts
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (B : Set (Fin n → K)) [Fintype B]
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K))) :
    (∑ b : B, vectorRank K A f b.val) =
      ∑ ℓ ∈ Finset.Icc 1 ℓbar, ℓ * (rankSubset K A f B ℓ).ncard := by
  classical
  have hcard (ℓ : ℕ) : (rankSubset K A f B ℓ).ncard =
      ∑ b : B, if vectorRank K A f b.val = ℓ then 1 else 0 := by
    let e : {u // u ∈ B ∧ vectorRank K A f u = ℓ} ≃
        {b : B // vectorRank K A f b.val = ℓ} :=
      { toFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
        invFun := fun b => ⟨b.val.val, b.val.property, b.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change Nat.card {u // u ∈ B ∧ vectorRank K A f u = ℓ} = _
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hz : b.val = 0
  · simp [hz]
  · have hb := vectorRank_bounds K A f b.val hz (hker b.property)
    simp [mul_ite, eq_comm, Finset.mem_Icc, hb.1, hb.2]

/-- Equation (11): the multiplicity is the rank-weighted number of basis generators. -/
theorem IsJordanKrylovBasis.sum_rankCounts_eq_charpoly_multiplicity
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (hfull : powerKernel K A f n ≤ powerKernel K A f ℓbar)
    (B : Set (Fin n → K))
    (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B) :
    (∑ ℓ ∈ Finset.Icc 1 ℓbar, ℓ * (rankSubset K A f B ℓ).ncard) =
      multiplicity f A.charpoly := by
  classical
  let : Fintype B := hB.2.1.fintype
  rw [← sum_ranks_eq_sum_rankCounts K A f B (hB.1.subset K A _ B)]
  exact hB.sum_ranks_eq_charpoly_multiplicity K A f hf hm hfull B

/-- The stopping criterion in the paper's rank-count notation. -/
theorem IsJordanKrylovIndependent.isBasis_of_sum_rankCounts_eq
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (hsum : (∑ ℓ ∈ Finset.Icc 1 ℓbar, ℓ * (rankSubset K A f B ℓ).ncard) =
      multiplicity f A.charpoly) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B := by
  classical
  let : Fintype B := hB.1.fintype
  apply hB.isBasis_of_sum_ranks_eq K A f hf hm B hker
  rw [sum_ranks_eq_sum_rankCounts K A f B hker]
  exact hsum

end SympyProofs.JordanKrylov
