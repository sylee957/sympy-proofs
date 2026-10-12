import SympyProofs.JordanKrylov.Mathematics.KrylovSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.DirectSum.Module

/-!
# Krylov spaces for a power of an irreducible polynomial

The first degree-f block is independent and its nonzero vectors all have
the same f-rank. The blocks obtained by applying successive powers of f(A)
give an independent spanning family and a direct-sum decomposition.
Directness is expressed using `iSupIndep` and a linear equivalence from mathlib's direct sum.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators DirectSum

/-- A vector in the truncated space is a polynomial of degree below d applied to u. -/
theorem mem_truncatedKrylovSpace_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) (d : ℕ) :
    v ∈ truncatedKrylovSpace K A u d ↔
      ∃ q : K[X], q.degree < d ∧ (aeval A q) *ᵥ u = v := by
  classical
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    refine ⟨∑ i : Fin d, C (c i) * X ^ (i : ℕ), degree_sum_fin_lt c, ?_⟩
    simpa [map_sum, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, krylovVector] using hc
  · rintro ⟨q, hq, rfl⟩
    have he : q = ∑ i : Fin d, C (q.coeff i) * X ^ (i : ℕ) := by
      simpa only [C_mul_X_pow_eq_monomial, sum_monomial_eq] using
        (Polynomial.sum_fin (fun i a => monomial i a) (by simp) hq).symm
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun i => q.coeff i, ?_⟩
    conv_rhs => rw [he]
    simp [map_sum, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, krylovVector]

/-- A nonzero polynomial of degree below an irreducible f is invertible on ker f(A)^ℓ. -/
theorem low_degree_aeval_injective_on_kernel (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f q : K[X]) (hf : Irreducible f)
    (hq : q ≠ 0) (hd : q.degree < f.degree) (ℓ : ℕ) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓ) (hz : (aeval A q) *ᵥ u = 0) : u = 0 := by
  have hcop : IsCoprime f q := hf.coprime_iff_not_dvd.mpr
    (fun hdiv => (not_le_of_gt hd) (degree_le_of_dvd hdiv hq))
  obtain ⟨a, b, hab⟩ := hcop.pow_left (m := ℓ)
  have he := congrArg (fun p : K[X] => (aeval A p) *ᵥ u) hab
  have hfu := (mem_powerKernel K A f ℓ u).mp hu
  simpa [map_add, map_mul, map_pow, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    hfu, hz] using he.symm

/-- The first deg(f) Krylov vectors of a nonzero f-primary vector are independent. -/
theorem truncatedKrylov_linearIndependent (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓ) :
    LinearIndependent K (fun i : Fin f.natDegree => krylovVector A u i) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  let q : K[X] := ∑ j : Fin f.natDegree, C (c j) * X ^ (j : ℕ)
  have hqann : (aeval A q) *ᵥ u = 0 := by
    simpa [q, map_sum, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, krylovVector] using hc
  have hq : q = 0 := by
    by_contra hne
    apply hu0
    apply low_degree_aeval_injective_on_kernel K A f q hf hne _ ℓ u hu hqann
    simpa [degree_eq_natDegree hf.ne_zero] using degree_sum_fin_lt c
  have hcoeff := congrArg (fun p : K[X] => p.coeff i) hq
  simpa [q, C_mul_X_pow_eq_monomial, coeff_monomial, Fin.val_eq_val,
    Finset.sum_ite_eq'] using hcoeff

/-- Every nonzero vector in the first Krylov block has the same f-rank as u. -/
theorem vectorRank_eq_of_mem_truncatedKrylovSpace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (v : Fin n → K)
    (hv : v ∈ truncatedKrylovSpace K A u f.natDegree) (hv0 : v ≠ 0) :
    vectorRank K A f v = ℓ := by
  have hvker : v ∈ powerKernel K A f ℓbar :=
    truncatedKrylovSpace_le_powerKernel K A f u f.natDegree ℓbar hu hv
  obtain ⟨q, hd, hqv⟩ := (mem_truncatedKrylovSpace_iff K A u v f.natDegree).mp hv
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqv; exact hv0 hqv.symm
  have hsame (k : ℕ) : v ∈ powerKernel K A f k ↔ u ∈ powerKernel K A f k := by
    have hc : Commute ((aeval A f) ^ k) (aeval A q) := by
      simpa using (Commute.all (f ^ k) q).map (aeval A)
    have hku : ((aeval A f) ^ k) *ᵥ u ∈ powerKernel K A f ℓbar := by
      rw [mem_powerKernel, Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm,
        pow_add, ← Matrix.mulVec_mulVec, (mem_powerKernel K A f ℓbar u).mp hu,
        Matrix.mulVec_zero]
    rw [← hqv, mem_powerKernel, mem_powerKernel, Matrix.mulVec_mulVec, hc.eq,
      ← Matrix.mulVec_mulVec]
    constructor
    · intro hz
      exact low_degree_aeval_injective_on_kernel K A f q hf hq0
        (by simpa [degree_eq_natDegree hf.ne_zero] using hd) ℓbar _ hku hz
    · intro hz; rw [hz, Matrix.mulVec_zero]
  have hpos : 1 ≤ ℓ := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hqv; exact hv0 hqv.symm
    simpa [hrank] using (vectorRank_bounds K A f u hu0 hu).1
  rw [vectorRank_eq_iff K A f v hvker hpos]
  have hur := (vectorRank_eq_iff K A f u hu hpos).mp hrank
  exact ⟨(hsame ℓ).mpr hur.1, fun h => hur.2 ((hsame (ℓ - 1)).mp h)⟩

/-- The i-th block in the paper's direct sum, written as a linear image. -/
noncomputable def krylovLayer (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (i : ℕ) :
    Submodule K (Fin n → K) :=
  (truncatedKrylovSpace K A u f.natDegree).map ((aeval A f) ^ i).mulVecLin

/-- Commutation identifies the image block with a truncated Krylov space. -/
theorem krylovLayer_eq (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (i : ℕ) :
    krylovLayer K A f u i =
      truncatedKrylovSpace K A (((aeval A f) ^ i) *ᵥ u) f.natDegree := by
  unfold krylovLayer truncatedKrylovSpace krylovVectors
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext j
  change (aeval A f) ^ i *ᵥ (A ^ (j : ℕ) *ᵥ u) =
    A ^ (j : ℕ) *ᵥ ((aeval A f) ^ i *ᵥ u)
  simp only [Matrix.mulVec_mulVec]
  rw [((commute_aeval_pow K A f i).pow_left (j : ℕ)).eq]

/-- Every vector in the full Krylov space is h(A)u for some polynomial h. -/
theorem mem_krylovSpace_iff (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    v ∈ krylovSpace K A u ↔ ∃ q : K[X], (aeval A q) *ᵥ u = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      exact ⟨X ^ k, by simp [krylovVector]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨p, rfl⟩ := ihx
      obtain ⟨q, rfl⟩ := ihy
      exact ⟨p + q, by simp [Matrix.add_mulVec]⟩
    | smul a x hx ih =>
      obtain ⟨p, rfl⟩ := ih
      exact ⟨C a * p, by simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]⟩
  · rintro ⟨q, rfl⟩
    have h := (mem_truncatedKrylovSpace_iff K A u ((aeval A q) *ᵥ u)
      (q.natDegree + 1)).mpr ⟨q, lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self _), rfl⟩
    exact truncatedKrylovSpace_le_krylovSpace K A u _ h

/-- Polynomial division by f separates the first block from the remaining Krylov space. -/
theorem krylovSpace_eq_sup (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic) (u : Fin n → K) :
    krylovSpace K A u = truncatedKrylovSpace K A u f.natDegree ⊔
      krylovSpace K A ((aeval A f) *ᵥ u) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨q, rfl⟩ := (mem_krylovSpace_iff K A u v).mp hv
    apply Submodule.mem_sup.mpr
    refine ⟨(aeval A (q %ₘ f)) *ᵥ u, ?_,
      (aeval A (q /ₘ f)) *ᵥ ((aeval A f) *ᵥ u), ?_, ?_⟩
    · exact (mem_truncatedKrylovSpace_iff K A u _ _).mpr
        ⟨q %ₘ f, (degree_modByMonic_lt q hf).trans_le degree_le_natDegree, rfl⟩
    · exact (mem_krylovSpace_iff K A _ _).mpr ⟨q /ₘ f, rfl⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, ← Matrix.add_mulVec, ← map_add,
        mul_comm (q /ₘ f) f, modByMonic_add_div]
  · apply sup_le (truncatedKrylovSpace_le_krylovSpace K A u _)
    apply krylovSpace_le K A _ _
    · exact (mem_krylovSpace_iff K A u _).mpr ⟨f, rfl⟩
    · exact fun v hv => mulVec_mem_krylovSpace K A u v hv

/-- The blocks span the whole Krylov space whenever f(A)^ℓu = 0. -/
theorem krylovSpace_eq_iSup_layers (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic)
    (ℓ : ℕ) (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ) :
    krylovSpace K A u = ⨆ i : Fin ℓ, krylovLayer K A f u i := by
  induction ℓ generalizing u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    subst u
    simp [krylovSpace, krylovVector]
  | succ ℓ ih =>
    have hnext : (aeval A f) *ᵥ u ∈ powerKernel K A f ℓ := by
      rw [mem_powerKernel, Matrix.mulVec_mulVec, ← pow_succ]
      exact (mem_powerKernel K A f (ℓ + 1) u).mp hu
    have hsplit : (⨆ i : Fin (ℓ + 1), krylovLayer K A f u i) =
        krylovLayer K A f u 0 ⊔ ⨆ i : Fin ℓ, krylovLayer K A f u (i.val + 1) := by
      apply le_antisymm
      · apply iSup_le
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact (le_iSup (fun j : Fin ℓ => krylovLayer K A f u (j.val + 1)) j).trans le_sup_right
      · apply sup_le (le_iSup (fun i : Fin (ℓ + 1) => krylovLayer K A f u i) 0)
        exact iSup_le fun i => le_iSup (fun j : Fin (ℓ + 1) => krylovLayer K A f u j) i.succ
    rw [krylovSpace_eq_sup K A f hf, ih _ hnext, hsplit]
    congr 1
    · simp [krylovLayer_eq]
    · apply iSup_congr
      intro i
      simp only [krylovLayer_eq, Matrix.mulVec_mulVec, pow_succ]


private theorem iterate_mem_kernel (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓ) (i : ℕ) (hi : i ≤ ℓ) :
    (aeval A f) ^ i *ᵥ u ∈ powerKernel K A f (ℓ - i) := by
  rw [mem_powerKernel, Matrix.mulVec_mulVec, ← pow_add, Nat.sub_add_cancel hi]
  exact (mem_powerKernel K A f ℓ u).mp hu

theorem krylovLayer_le_powerKernel (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓ) (i : ℕ) (hi : i ≤ ℓ) :
    krylovLayer K A f u i ≤ powerKernel K A f (ℓ - i) := by
  rw [krylovLayer_eq]
  exact truncatedKrylovSpace_le_powerKernel K A f _ _ _
    (iterate_mem_kernel K A f u hu i hi)

private theorem layer_eq_zero_of_mem_previous_kernel (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ)
    (hprev : u ∉ powerKernel K A f (ℓ - 1))
    (i : Fin ℓ) (v : Fin n → K) (hv : v ∈ krylovLayer K A f u i)
    (hz : v ∈ powerKernel K A f (ℓ - 1 - i.val)) : v = 0 := by
  rw [krylovLayer_eq] at hv
  obtain ⟨q, hd, hqv⟩ := (mem_truncatedKrylovSpace_iff K A _ v _).mp hv
  by_cases hq0 : q = 0
  · simpa [hq0] using hqv.symm
  have hcomm : Commute ((aeval A f) ^ (ℓ - 1 - i.val)) (aeval A q) := by
    simpa using (Commute.all (f ^ (ℓ - 1 - i.val)) q).map (aeval A)
  have he : ℓ - 1 - i.val + i.val = ℓ - 1 := by omega
  rw [← hqv, mem_powerKernel, Matrix.mulVec_mulVec, hcomm.eq,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec u, ← pow_add, he] at hz
  have hlast := iterate_mem_kernel K A f u hu (ℓ - 1) (by omega)
  have hzlast := low_degree_aeval_injective_on_kernel K A f q hf hq0
    (by simpa [degree_eq_natDegree hf.ne_zero] using hd) _ _ hlast hz
  exact False.elim (hprev ((mem_powerKernel K A f (ℓ - 1) u).mpr hzlast))

/-- The summands are independent; this is the directness part of ⊕. -/
theorem krylovLayers_independent (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ)
    (hprev : u ∉ powerKernel K A f (ℓ - 1)) :
    iSupIndep (fun i : Fin ℓ => krylovLayer K A f u i) := by
  classical
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s v hv hsum
  have hall : ∀ t : ℕ, ∀ i : Fin ℓ, i.val = t → i ∈ s → v i = 0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i hit his
      apply layer_eq_zero_of_mem_previous_kernel K A f hf u hu hprev i (v i) (hv i his)
      rw [mem_powerKernel]
      have he := congrArg (((aeval A f) ^ (ℓ - 1 - i.val)).mulVecLin) hsum
      simp only [map_sum, map_zero, Matrix.mulVecLin_apply] at he
      have hsingle : (∑ j ∈ s, (aeval A f) ^ (ℓ - 1 - i.val) *ᵥ v j) =
          (aeval A f) ^ (ℓ - 1 - i.val) *ᵥ v i := by
        apply Finset.sum_eq_single i
        · intro j hjs hji
          by_cases hj : j.val < i.val
          · rw [ih j.val (by omega) j rfl hjs, Matrix.mulVec_zero]
          · have hij : i.val < j.val := by
              have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
              omega
            have hjker := krylovLayer_le_powerKernel K A f u hu j.val (by omega) (hv j hjs)
            exact (mem_powerKernel K A f _ _).mp
              (powerKernel_le K A f (by omega : ℓ - j.val ≤ ℓ - 1 - i.val) hjker)
        · exact fun h => False.elim (h his)
      exact hsingle.symm.trans he
  exact fun i hi => hall i.val i rfl hi

/-- The displayed decomposition: equality of the sum and independence of its summands. -/
theorem krylovSpace_directSum (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) :
    krylovSpace K A u = (⨆ i : Fin ℓ, krylovLayer K A f u i) ∧
      iSupIndep (fun i : Fin ℓ => krylovLayer K A f u i) := by
  have hpos : 1 ≤ ℓ := by simpa [hrank] using (vectorRank_bounds K A f u hu0 hu).1
  have h := (vectorRank_eq_iff K A f u hu hpos).mp hrank
  exact ⟨krylovSpace_eq_iSup_layers K A f hm ℓ u h.1,
    krylovLayers_independent K A f hf u h.1 h.2⟩


/-- The canonical direct-sum decomposition of the Krylov space. The forward map
adds the layer vectors; its inverse gives their unique decomposition. -/
noncomputable def krylovSpaceDirectSumEquiv (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) :
    (⨁ i : Fin ℓ, krylovLayer K A f u i) ≃ₗ[K] krylovSpace K A u := by
  classical
  let h := krylovSpace_directSum K A f hf hm u hu0 hu hrank
  exact (LinearEquiv.ofInjective
    (DirectSum.coeLinearMap (fun i : Fin ℓ => krylovLayer K A f u i))
    h.2.dfinsupp_lsum_injective).trans
    (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap.trans h.1.symm))

/-- The direct-sum equivalence sends a vector in a single layer to that same vector. -/
@[simp] theorem krylovSpaceDirectSumEquiv_lof (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (i : Fin ℓ) (v : krylovLayer K A f u i) :
    ((krylovSpaceDirectSumEquiv K A f hf hm u hu0 hu hrank
      (DirectSum.lof K (Fin ℓ) (fun j => krylovLayer K A f u j) i v)) :
      Fin n → K) = v := by
  change DirectSum.coeLinearMap (fun j : Fin ℓ => krylovLayer K A f u j)
    (DirectSum.lof K (Fin ℓ) (fun j => krylovLayer K A f u j) i v) = v
  exact DirectSum.coeLinearMap_lof (fun j : Fin ℓ => krylovLayer K A f u j) i v

/-- The combined family, indexed by block number and position within that block. -/
noncomputable def primaryKrylovFamily (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (ℓ : ℕ) :
    Fin ℓ × Fin f.natDegree → (Fin n → K) :=
  fun ij => krylovVector A (((aeval A f) ^ (ij.1 : ℕ)) *ᵥ u) ij.2

/-- The paper's union 𝓛_A(u) of the ℓ finite Krylov blocks. -/
noncomputable def primaryKrylovVectors (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (ℓ : ℕ) :
    Set (Fin n → K) :=
  ⋃ i : Fin ℓ, krylovVectors K A (((aeval A f) ^ (i : ℕ)) *ᵥ u) f.natDegree

theorem primaryKrylovVectors_eq_range (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) (ℓ : ℕ) :
    primaryKrylovVectors K A f u ℓ = Set.range (primaryKrylovFamily K A f u ℓ) := by
  ext v
  simp only [primaryKrylovVectors, Set.mem_iUnion, krylovVectors, Set.mem_range,
    primaryKrylovFamily, Prod.exists]

theorem span_primaryKrylovVectors (K : Subfield ℂ) {n ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓ) :
    Submodule.span K (primaryKrylovVectors K A f u ℓ) = krylovSpace K A u := by
  rw [primaryKrylovVectors, Submodule.span_iUnion]
  simpa only [krylovLayer_eq, truncatedKrylovSpace] using
    (krylovSpace_eq_iSup_layers K A f hf ℓ u hu).symm

/-- The combined family 𝓛_A(u) is linearly independent. -/
theorem primaryKrylovFamily_linearIndependent (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) :
    LinearIndependent K (primaryKrylovFamily K A f u ℓ) := by
  classical
  have hpos : 1 ≤ ℓ := by simpa [hrank] using (vectorRank_bounds K A f u hu0 hu).1
  have h := (vectorRank_eq_iff K A f u hu hpos).mp hrank
  have hind (i : Fin ℓ) : LinearIndependent K
      (fun j : Fin f.natDegree => primaryKrylovFamily K A f u ℓ (i, j)) := by
    apply truncatedKrylov_linearIndependent K A f hf _ _
      (iterate_mem_kernel K A f u h.1 i.val (by omega))
    intro hz
    apply h.2
    exact powerKernel_le K A f (by omega : i.val ≤ ℓ - 1)
      ((mem_powerKernel K A f i.val u).mpr hz)
  refine Fintype.linearIndependent_iff.mpr fun c hc ij => ?_
  have hmem (i : Fin ℓ) : (∑ j : Fin f.natDegree,
      c (i, j) • primaryKrylovFamily K A f u ℓ (i, j)) ∈ krylovLayer K A f u i := by
    rw [krylovLayer_eq]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, rfl⟩
  have hsum : (∑ i : Fin ℓ, ∑ j : Fin f.natDegree,
      c (i, j) • primaryKrylovFamily K A f u ℓ (i, j)) = 0 := by
    simpa only [Fintype.sum_prod_type] using hc
  have hblocks := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (krylovLayers_independent K A f hf u h.1 h.2) Finset.univ
    (fun i => ∑ j : Fin f.natDegree, c (i, j) • primaryKrylovFamily K A f u ℓ (i, j))
    (fun i _ => hmem i) hsum ij.1 (Finset.mem_univ _)
  exact Fintype.linearIndependent_iff.mp (hind ij.1) (fun j => c (ij.1, j)) hblocks ij.2

theorem primaryKrylovVectors_linearIndepOn (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) :
    LinearIndepOn K id (primaryKrylovVectors K A f u ℓ) := by
  rw [primaryKrylovVectors_eq_range]
  exact (primaryKrylovFamily_linearIndependent K A f hf u hu0 hu hrank).linearIndepOn_id


/-- The Krylov space has dimension ℓ · deg f. -/
theorem finrank_krylovSpace (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) :
    Module.finrank K (krylovSpace K A u) = ℓ * f.natDegree := by
  have hur : u ∈ powerKernel K A f ℓ := by
    simpa [hrank] using mem_powerKernel_vectorRank K A f u hu
  rw [← span_primaryKrylovVectors K A f hm u hur, primaryKrylovVectors_eq_range]
  simpa using finrank_span_eq_card
    (primaryKrylovFamily_linearIndependent K A f hf u hu0 hu hrank)

/-- Applying f(A) i times lowers the f-rank by i, before the vector vanishes. -/
theorem vectorRank_pow_mulVec (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (i : ℕ) (hi : i < ℓ) :
    vectorRank K A f ((aeval A f) ^ i *ᵥ u) = ℓ - i := by
  have hpos : 1 ≤ ℓ := by
    simpa [hrank] using (vectorRank_bounds K A f u hu0 hu).1
  have hur := (vectorRank_eq_iff K A f u hu hpos).mp hrank
  have hw := iterate_mem_kernel K A f u hur.1 i (by omega)
  apply (vectorRank_eq_iff K A f _ hw (by omega : 1 ≤ ℓ - i)).mpr
  refine ⟨hw, ?_⟩
  intro hprev
  apply hur.2
  have hz := (mem_powerKernel K A f (ℓ - i - 1) _).mp hprev
  apply (mem_powerKernel K A f (ℓ - 1) u).mpr
  rw [Matrix.mulVec_mulVec, ← pow_add] at hz
  have he : ℓ - i - 1 + i = ℓ - 1 := by omega
  simpa only [he] using hz

/-- Every nonzero vector in the i-th layer has f-rank ℓ - i.
This includes the paper's range 1 ≤ i ≤ ℓ - 1, as well as i = 0. -/
theorem vectorRank_eq_of_mem_krylovLayer (K : Subfield ℂ) {n ℓbar ℓ : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (u : Fin n → K) (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f u = ℓ) (i : ℕ) (hi : i < ℓ)
    (v : Fin n → K) (hv : v ∈ krylovLayer K A f u i) (hv0 : v ≠ 0) :
    vectorRank K A f v = ℓ - i := by
  have hur : u ∈ powerKernel K A f ℓ := by
    simpa [hrank] using mem_powerKernel_vectorRank K A f u hu
  rw [krylovLayer_eq] at hv
  exact vectorRank_eq_of_mem_truncatedKrylovSpace K A f hf _
    (iterate_mem_kernel K A f u hur i (by omega))
    (vectorRank_pow_mulVec K A f u hu0 hu hrank i hi) v hv hv0

end SympyProofs.JordanKrylov
