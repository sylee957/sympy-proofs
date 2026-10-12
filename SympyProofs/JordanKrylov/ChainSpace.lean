import SympyProofs.JordanKrylov.JordanChain
import SympyProofs.JordanKrylov.KrylovDecomposition
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Spaces spanned by the Jordan chains

The chain spaces live over ℂ. Scalar extension of the Krylov space is
represented concretely by the complex span of its embedded vectors.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators DirectSum TensorProduct

/-- The paper's P_A(α,u), with generators ordered p^(ℓ), p^(ℓ-1), …, p^(1). -/
noncomputable def chainSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) (α : ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (Set.range (fun j : Fin ℓ => pChainAt K A f ℓ (ℓ - j.val) α u))

/-- The direct sum of chain spaces over a supplied list of evaluation points.
Reducibility lets this type inherit mathlib's direct-sum vector-space instances. -/
@[reducible] noncomputable def indexedRootChainSpace (K : Subfield ℂ) {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) (α : Fin d → ℂ) : Type :=
  ⨁ i : Fin d, chainSpace K A f u ℓ (α i)

/-- The paper's P_A(u), indexed directly by the complex roots of f.
For irreducible f over K ⊆ ℂ these roots are distinct. -/
@[reducible] noncomputable def rootChainSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) : Type := by
  classical
  exact ⨁ α : (f.map K.subtype).roots.toFinset, chainSpace K A f u ℓ α.val

/-- The image of the direct sum under addition in ℂⁿ, used for the dimension proof. -/
noncomputable def rootChainSpan (K : Subfield ℂ) {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) (α : Fin d → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ i, chainSpace K A f u ℓ (α i)

/-- The concrete scalar extension of L_A(u) inside ℂⁿ. -/
noncomputable def complexKrylovSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun v : Fin n → K => fun j => K.subtype (v j)) ''
    (krylovSpace K A u : Set (Fin n → K)))

/-- Vectors of successive exact nilpotency orders are linearly independent. -/
theorem linearIndependent_of_exact_orders {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {ℓ : ℕ} (v : Fin ℓ → V)
    (hz : ∀ j, (T ^ (j.val + 1)) (v j) = 0)
    (hne : ∀ j, (T ^ j.val) (v j) ≠ 0) : LinearIndependent ℂ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hall : ∀ m : ℕ, ∀ i : Fin ℓ, ℓ - 1 - i.val = m → c i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him
      have he := congrArg (T ^ i.val) hc
      simp only [map_sum, map_smul, map_zero] at he
      have hs : (∑ j : Fin ℓ, c j • (T ^ i.val) (v j)) =
          c i • (T ^ i.val) (v i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          by_cases hij : i.val < j.val
          · rw [ih (ℓ - 1 - j.val) (by omega) j rfl, zero_smul]
          · have hji' : j.val < i.val := by
              have : j.val ≠ i.val := fun h => hji (Fin.ext h)
              omega
            have heq : i.val = (i.val - (j.val + 1)) + (j.val + 1) := by omega
            rw [heq, pow_add, Module.End.mul_apply, hz j, map_zero, smul_zero]
        · simp
      rw [hs] at he
      exact (smul_eq_zero.mp he).resolve_right (hne i)
  intro i
  exact hall _ i rfl

private theorem matrix_end_pow_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (v : Fin n → ℂ) : (B.mulVecLin ^ k) v = B ^ k *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih => simp [pow_succ, Module.End.mul_apply, ih, Matrix.mulVec_mulVec]

/-- Each chain is an independent family of ℓ vectors. -/
theorem chainVectors_linearIndependent (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    LinearIndependent ℂ (fun j : Fin ℓ => pChainAt K A f ℓ (ℓ - j.val) α u) := by
  have hasc : LinearIndependent ℂ
      (fun j : Fin ℓ => pChainAt K A f ℓ (j.val + 1) α u) := by
    apply linearIndependent_of_exact_orders (A.map K.subtype - α • 1).mulVecLin
    · intro j
      rw [matrix_end_pow_apply]
      exact pChainAt_pow_eq_zero K A f u hu hrank α hα (by omega)
    · intro j
      rw [matrix_end_pow_apply]
      simpa using pChainAt_pow_pred_ne_zero K A f hf u hu hrank α hα
        (by omega : 1 ≤ j.val + 1) (by omega : j.val + 1 ≤ ℓ)
  have hrev : (fun j : Fin ℓ => pChainAt K A f ℓ (j.val + 1) α u) ∘ Fin.rev =
      (fun j : Fin ℓ => pChainAt K A f ℓ (ℓ - j.val) α u) := by
    funext j
    simp only [Function.comp_apply, Fin.val_rev]
    congr 1
    omega
  rw [← hrev]
  exact hasc.comp Fin.rev Fin.rev_injective

/-- Each root contributes a chain space of complex dimension ℓ. -/
theorem finrank_chainSpace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    Module.finrank ℂ (chainSpace K A f u ℓ α) = ℓ := by
  unfold chainSpace
  rw [finrank_span_eq_card (chainVectors_linearIndependent K A f hf u hu hrank α hα)]
  exact Fintype.card_fin ℓ

/-- A chain space lies in the generalized eigenspace of its root. -/
theorem chainSpace_le_maxGenEigenspace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓbar) (hrank : vectorRank K A f u = ℓ)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    chainSpace K A f u ℓ α ≤ Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin α := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨ℓ - j.val, ?_⟩
  rw [LinearMap.mem_ker]
  have he : (A.map K.subtype).mulVecLin - α • 1 =
      (A.map K.subtype - α • 1).mulVecLin := by ext v i; simp
  rw [he, matrix_end_pow_apply]
  exact pChainAt_pow_eq_zero K A f u hu hrank α hα (by omega)

/-- Distinct roots give independent chain spaces. -/
theorem chainSpaces_independent (K : Subfield ℂ) {n ℓbar ℓ d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓbar) (hrank : vectorRank K A f u = ℓ)
    (α : Fin d → ℂ) (hinj : Function.Injective α)
    (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    iSupIndep (fun i => chainSpace K A f u ℓ (α i)) :=
  ((Module.End.independent_maxGenEigenspace (A.map K.subtype).mulVecLin).comp hinj).mono
    (fun i => chainSpace_le_maxGenEigenspace K A f u hu hrank (α i) (hroot i))

/-- Addition identifies P_A(u) with its image in ℂⁿ when the roots are distinct. -/
noncomputable def rootChainSpaceEquivSpan (K : Subfield ℂ) {n ℓbar ℓ d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓbar) (hrank : vectorRank K A f u = ℓ)
    (α : Fin d → ℂ) (hinj : Function.Injective α)
    (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    indexedRootChainSpace K A f u ℓ α ≃ₗ[ℂ] rootChainSpan K A f u ℓ α := by
  classical
  exact (LinearEquiv.ofInjective (DirectSum.coeLinearMap _)
    (chainSpaces_independent K A f u hu hrank α hinj hroot).dfinsupp_lsum_injective).trans
    (LinearEquiv.ofEq _ _ DirectSum.range_coeLinearMap)

/-- The chain spaces at d distinct roots have total dimension ℓd. -/
theorem finrank_rootChainSpan (K : Subfield ℂ) {n ℓbar ℓ d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin d → ℂ)
    (hinj : Function.Injective α) (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    Module.finrank ℂ (rootChainSpan K A f u ℓ α) = ℓ * d := by
  rw [← (rootChainSpaceEquivSpan K A f u hu hrank α hinj hroot).finrank_eq,
    Module.finrank_directSum]
  simp [finrank_chainSpace K A f hf u hu hrank, hroot, Nat.mul_comm]

/-- The direct sum P_A(u) has dimension ℓd. -/
theorem finrank_rootChainSpace (K : Subfield ℂ) {n ℓbar ℓ d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin d → ℂ)
    (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    Module.finrank ℂ (indexedRootChainSpace K A f u ℓ α) = ℓ * d := by
  rw [Module.finrank_directSum]
  simp [finrank_chainSpace K A f hf u hu hrank, hroot, Nat.mul_comm]

/-- Coordinatewise inclusion Kⁿ → ℂⁿ, as a K-linear map. -/
noncomputable def complexVectorMap (K : Subfield ℂ) (n : ℕ) : (Fin n → K) →ₗ[K] (Fin n → ℂ) where
  toFun v j := K.subtype (v j)
  map_add' _ _ := by ext; simp
  map_smul' a v := by ext i; exact (K.subtype.map_mul a (v i))

private theorem span_complexVectorMap_span (K : Subfield ℂ) {n : ℕ}
    (s : Set (Fin n → K)) :
    Submodule.span ℂ (complexVectorMap K n '' (Submodule.span K s : Set (Fin n → K))) =
      Submodule.span ℂ (complexVectorMap K n '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span ⟨v, hv, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [map_smul]
      exact (Submodule.restrictScalars K (Submodule.span ℂ (complexVectorMap K n '' s))).smul_mem a ih
  · apply Submodule.span_mono
    exact Set.image_mono Submodule.subset_span

/-- Any finite spanning family of L_A(u) spans its concrete complexification. -/
theorem complexKrylovSpace_eq_span_primary (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ) :
    complexKrylovSpace K A u = Submodule.span ℂ
      (Set.range (fun ij => complexVectorMap K n (primaryKrylovFamily K A f u ℓ ij))) := by
  change Submodule.span ℂ (complexVectorMap K n '' (krylovSpace K A u : Set _)) = _
  rw [← span_primaryKrylovVectors K A f hm u hu, span_complexVectorMap_span,
    primaryKrylovVectors_eq_range]
  congr 1
  ext v
  simp

/-- Scalar extension cannot increase the dimension of this finite spanning family. -/
theorem finrank_complexKrylovSpace_le (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ) :
    Module.finrank ℂ (complexKrylovSpace K A u) ≤ ℓ * f.natDegree := by
  rw [complexKrylovSpace_eq_span_primary K A f hm u hu]
  have h := finrank_range_le_card (R := ℂ)
    (fun ij => complexVectorMap K n (primaryKrylovFamily K A f u ℓ ij))
  simpa only [Set.finrank, Fintype.card_prod, Fintype.card_fin] using h

private theorem complexKrylovSpace_aeval_mem (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (q : ℂ[X])
    (v : Fin n → ℂ) (hv : v ∈ complexKrylovSpace K A u) :
    aeval (A.map K.subtype) q *ᵥ v ∈ complexKrylovSpace K A u := by
  have hinv : ∀ v ∈ complexKrylovSpace K A u,
      (A.map K.subtype) *ᵥ v ∈ complexKrylovSpace K A u := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, hw, rfl⟩ := hv
      have he : A.map K.subtype *ᵥ (fun i => K.subtype (w i)) =
          fun i => K.subtype ((A *ᵥ w) i) := by
        simpa only [Function.comp_def] using (funext (RingHom.map_mulVec K.subtype A w)).symm
      rw [he]
      exact Submodule.subset_span ⟨A *ᵥ w, mulVec_mem_krylovSpace K A u w hw, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a ih
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hp hq
  | monomial k c =>
    have hpow : ∀ k, (A.map K.subtype) ^ k *ᵥ v ∈ complexKrylovSpace K A u := by
      intro k
      induction k with
      | zero => simpa using hv
      | succ k ih => simpa [pow_succ', ← Matrix.mulVec_mulVec] using hinv _ ih
    simpa [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec] using
      (complexKrylovSpace K A u).smul_mem c (hpow k)

/-- Every chain vector is in the complexified Krylov space. -/
theorem pChainAt_mem_complexKrylovSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ k : ℕ) (α : ℂ) : pChainAt K A f ℓ k α u ∈ complexKrylovSpace K A u := by
  rw [pChainAt_eq_formula, bivariateMatrix_scalar]
  apply complexKrylovSpace_aeval_mem
  have hw : (aeval A f) ^ (ℓ - k) *ᵥ u ∈ krylovSpace K A u := by
    apply (mem_krylovSpace_iff K A u _).mpr
    exact ⟨f ^ (ℓ - k), by rw [map_pow]⟩
  have he := funext (RingHom.map_mulVec K.subtype ((aeval A f) ^ (ℓ - k)) u)
  rw [Matrix.map_pow] at he
  have hmem : (fun i => K.subtype (((aeval A f) ^ (ℓ - k) *ᵥ u) i)) ∈
      complexKrylovSpace K A u := Submodule.subset_span ⟨_, hw, rfl⟩
  simpa only [he, Function.comp_def] using hmem

/-- The sum of chain spaces is contained in the complexification of L_A(u). -/
theorem rootChainSpan_le_complexKrylovSpace (K : Subfield ℂ) {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (ℓ : ℕ) (α : Fin d → ℂ) :
    rootChainSpan K A f u ℓ α ≤ complexKrylovSpace K A u := by
  apply iSup_le
  intro i
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact pChainAt_mem_complexKrylovSpace K A f u ℓ (ℓ - j.val) (α i)

/-- Lemma 8, as equality of subspaces of ℂⁿ. The roots are indexed without repetition
by Fin (deg f), as in the paper. -/
theorem rootChainSpan_eq_complexKrylovSpace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin f.natDegree → ℂ)
    (hinj : Function.Injective α) (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    rootChainSpan K A f u ℓ α = complexKrylovSpace K A u := by
  apply Submodule.eq_of_le_of_finrank_le (rootChainSpan_le_complexKrylovSpace K A f u ℓ α)
  rw [finrank_rootChainSpan K A f hf u hu hrank α hinj hroot]
  apply finrank_complexKrylovSpace_le K A f hm
  simpa [hrank] using mem_powerKernel_vectorRank K A f u hu

/-- Each chain space is precisely the spectral component of the complexified
Krylov space, using mathlib's maximal generalized eigenspace. -/
theorem chainSpace_eq_inf_maxGenEigenspace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin f.natDegree → ℂ)
    (hinj : Function.Injective α) (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0)
    (i : Fin f.natDegree) :
    chainSpace K A f u ℓ (α i) = complexKrylovSpace K A u ⊓
      Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin (α i) := by
  classical
  let C := fun j => chainSpace K A f u ℓ (α j)
  let G := fun j => Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin (α j)
  have hCG : ∀ j, C j ≤ G j := fun j =>
    chainSpace_le_maxGenEigenspace K A f u hu hrank (α j) (hroot j)
  have hind : iSupIndep G :=
    (Module.End.independent_maxGenEigenspace (A.map K.subtype).mulVecLin).comp hinj
  have hdis : Disjoint (G i) (⨆ j, ⨆ (_ : j ≠ i), C j) :=
    (hind i).mono_right (iSup_mono fun j => iSup_mono fun _ => hCG j)
  have hsplit : (⨆ j, C j) = C i ⊔ ⨆ j, ⨆ (_ : j ≠ i), C j := by
    apply le_antisymm
    · apply iSup_le
      intro j
      by_cases h : j = i
      · subst j; exact le_sup_left
      · exact (le_iSup_of_le j (le_iSup (fun _ : j ≠ i => C j) h)).trans le_sup_right
    · exact sup_le (le_iSup C i)
        (iSup_le fun j => iSup_le fun _ => le_iSup C j)
  rw [← rootChainSpan_eq_complexKrylovSpace K A f hf hm u hu hrank α hinj hroot]
  change C i = (⨆ j, C j) ⊓ G i
  rw [hsplit, sup_inf_assoc_of_le _ (hCG i), hdis.symm.eq_bot, sup_bot_eq]

/-- The paper's spectral decomposition, expressed with mathlib's generalized eigenspaces.
The second conjunct states that the spectral components form a direct sum. -/
theorem complexKrylovSpace_spectral_decomposition (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin f.natDegree → ℂ)
    (hinj : Function.Injective α) (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    complexKrylovSpace K A u = (⨆ i, complexKrylovSpace K A u ⊓
      Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin (α i)) ∧
    iSupIndep (fun i => complexKrylovSpace K A u ⊓
      Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin (α i)) := by
  simp_rw [← chainSpace_eq_inf_maxGenEigenspace K A f hf hm u hu hrank α hinj hroot]
  exact ⟨(rootChainSpan_eq_complexKrylovSpace K A f hf hm u hu hrank α hinj hroot).symm,
    chainSpaces_independent K A f u hu hrank α hinj hroot⟩

/-- The natural map ℂ ⊗[K] L_A(u) → ℂ L_A(u), sending c ⊗ v to c • v. -/
noncomputable def krylovTensorToComplexSpan (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    ℂ ⊗[K] krylovSpace K A u →ₗ[ℂ] complexKrylovSpace K A u := by
  let inclusion : krylovSpace K A u →ₗ[K] complexKrylovSpace K A u :=
    ((complexVectorMap K n).comp (krylovSpace K A u).subtype).codRestrict
      ((complexKrylovSpace K A u).restrictScalars K)
      (fun v => Submodule.subset_span ⟨v.val, v.property, rfl⟩)
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • inclusion
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => smul_assoc _ _ _ }

@[simp] theorem krylovTensorToComplexSpan_tmul (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (c : ℂ) (v : krylovSpace K A u) :
    (krylovTensorToComplexSpan K A u (c ⊗ₜ[K] v) : Fin n → ℂ) =
      c • complexVectorMap K n v := rfl

theorem krylovTensorToComplexSpan_surjective (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    Function.Surjective (krylovTensorToComplexSpan K A u) := by
  let g := (complexKrylovSpace K A u).subtype.comp (krylovTensorToComplexSpan K A u)
  have hle : complexKrylovSpace K A u ≤ LinearMap.range g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨1 ⊗ₜ[K] (⟨v, hv⟩ : krylovSpace K A u), ?_⟩
    change (krylovTensorToComplexSpan K A u
      (1 ⊗ₜ[K] (⟨v, hv⟩ : krylovSpace K A u)) : Fin n → ℂ) = _
    simp [complexVectorMap]
  intro v
  obtain ⟨x, hx⟩ := hle v.property
  exact ⟨x, Subtype.ext hx⟩

/-- The direct sum is linearly isomorphic to the scalar-extension tensor product. -/
theorem rootChainSpaceTensorEquiv (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (α : Fin f.natDegree → ℂ)
    (hinj : Function.Injective α) (hroot : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    Nonempty (indexedRootChainSpace K A f u ℓ α ≃ₗ[ℂ] (ℂ ⊗[K] krylovSpace K A u)) := by
  have hdim : Module.finrank ℂ (ℂ ⊗[K] krylovSpace K A u) =
      Module.finrank ℂ (complexKrylovSpace K A u) := by
    rw [Module.finrank_baseChange, finrank_krylovSpace K A f hf hm u hu0 hu hrank,
      ← rootChainSpan_eq_complexKrylovSpace K A f hf hm u hu hrank α hinj hroot,
      finrank_rootChainSpan K A f hf u hu hrank α hinj hroot]
  have hsurj := krylovTensorToComplexSpan_surjective K A u
  have hbij : Function.Bijective (krylovTensorToComplexSpan K A u) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  exact ⟨((rootChainSpaceEquivSpan K A f u hu hrank α hinj hroot).trans
    (LinearEquiv.ofEq _ _
      (rootChainSpan_eq_complexKrylovSpace K A f hf hm u hu hrank α hinj hroot))).trans
    (LinearEquiv.ofBijective (krylovTensorToComplexSpan K A u) hbij).symm⟩

end SympyProofs.JordanKrylov
