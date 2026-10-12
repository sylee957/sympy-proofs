import SympyProofs.JordanKrylov.Mathematics.RankMultiplicity

/-! # Extending a Jordan–Krylov independent set

Lemma 15: a primary vector can be added when its last nonzero f(A)-iterate
lies outside the sum of the terminal Krylov spaces of the existing generators.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped BigOperators

/-- The last nonzero f(A)-iterate of a nonzero primary vector. -/
noncomputable def terminalVector (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K) : Fin n → K :=
  (aeval A f) ^ (vectorRank K A f u - 1) *ᵥ u

@[simp] theorem terminalVector_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) : terminalVector K A f 0 = 0 := by
  simp [terminalVector]

theorem terminalVector_ne_zero (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu0 : u ≠ 0) (hu : u ∈ powerKernel K A f ℓbar) : terminalVector K A f u ≠ 0 := by
  have hpos := (vectorRank_bounds K A f u hu0 hu).1
  exact ((vectorRank_eq_iff K A f u hu hpos).mp rfl).2

theorem terminalVector_mem_powerKernel (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (u : Fin n → K)
    (hu : u ∈ powerKernel K A f ℓbar) : terminalVector K A f u ∈ powerKernel K A f 1 := by
  by_cases hz : u = 0
  · subst u; simp
  have hp := (vectorRank_bounds K A f u hz hu).1
  have hr := mem_powerKernel_vectorRank K A f u hu
  change (aeval A f)^1 *ᵥ ((aeval A f)^(vectorRank K A f u - 1) *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec, ← pow_add, show 1 + (vectorRank K A f u - 1) =
    vectorRank K A f u by omega]
  exact hr

/-- A polynomial in A preserves each Krylov space. -/
theorem aeval_mulVec_mem_krylovSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) (q : K[X])
    (hv : v ∈ krylovSpace K A u) : aeval A q *ᵥ v ∈ krylovSpace K A u := by
  obtain ⟨p, rfl⟩ := (mem_krylovSpace_iff K A u v).mp hv
  exact (mem_krylovSpace_iff K A u _).mpr ⟨q * p, by simp [map_mul, Matrix.mulVec_mulVec]⟩

/-- The vectors killed by f(A) in a primary cyclic space form its terminal Krylov space. -/
theorem krylovSpace_inf_powerKernel_eq_terminal (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u : Fin n → K) (hu : u ∈ powerKernel K A f ℓbar) :
    krylovSpace K A u ⊓ powerKernel K A f 1 = krylovSpace K A (terminalVector K A f u) := by
  by_cases hz : u = 0
  · subst u; simp
  let r := vectorRank K A f u
  have hp : 1 ≤ r := (vectorRank_bounds K A f u hz hu).1
  have hle : krylovSpace K A (terminalVector K A f u) ≤
      krylovSpace K A u ⊓ powerKernel K A f 1 := by
    apply le_inf
    · apply krylovSpace_le K A _ _
      · exact (mem_krylovSpace_iff K A u _).mpr ⟨f^(r-1), by simp [terminalVector, r, map_pow]⟩
      · exact fun v hv => mulVec_mem_krylovSpace K A u v hv
    · exact krylovSpace_le_powerKernel K A f _ 1 (terminalVector_mem_powerKernel K A f u hu)
  have hd := LinearMap.finrank_range_add_finrank_ker
    (((aeval A f)^1).mulVecLin.domRestrict (krylovSpace K A u))
  have hk := Submodule.finrank_map_subtype_eq (krylovSpace K A u)
    (LinearMap.ker (((aeval A f)^1).mulVecLin.domRestrict (krylovSpace K A u)))
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype] at hk
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ← hk] at hd
  change Module.finrank K ((krylovSpace K A u).map ((aeval A f)^1).mulVecLin) +
    Module.finrank K ↥(krylovSpace K A u ⊓ powerKernel K A f 1) = _ at hd
  rw [finrank_map_krylovSpace K A f hf hm u hu 1,
    finrank_krylovSpace K A f hf hm u hz hu rfl] at hd
  have ht := finrank_map_krylovSpace K A f hf hm u hu (r-1)
  rw [map_krylovSpace_aeval_pow] at ht
  change Module.finrank K (krylovSpace K A (terminalVector K A f u)) = (r - (r-1))*f.natDegree at ht
  rw [show r - (r-1) = 1 by omega, one_mul] at ht
  have he := congrArg (fun k => k * f.natDegree) (Nat.sub_add_cancel hp)
  simp only [Nat.add_mul, one_mul] at he
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [ht]
  change (r-1)*f.natDegree + _ = r*f.natDegree at hd
  omega

/-- A polynomial in A preserves a sum of Krylov spaces. -/
theorem aeval_mulVec_mem_iSup_krylovSpace (K : Subfield ℂ) {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) K) (u : ι → Fin n → K) (v : Fin n → K) (q : K[X])
    (hv : v ∈ ⨆ i, krylovSpace K A (u i)) :
    aeval A q *ᵥ v ∈ ⨆ i, krylovSpace K A (u i) := by
  have hle : (⨆ i, krylovSpace K A (u i)) ≤
      (⨆ i, krylovSpace K A (u i)).comap (aeval A q).mulVecLin := by
    apply iSup_le
    intro i x hx
    exact (le_iSup (fun i => krylovSpace K A (u i)) i)
      (aeval_mulVec_mem_krylovSpace K A (u i) x q hx)
  exact hle hv

/-- In an independent sum of primary cyclic spaces, the kernel of f(A) is the
sum of the terminal cyclic spaces. -/
theorem iSup_krylovSpace_inf_powerKernel (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K))) :
    (⨆ b : B, krylovSpace K A b.val) ⊓ powerKernel K A f 1 =
      ⨆ b : B, krylovSpace K A (terminalVector K A f b.val) := by
  classical
  let : Fintype B := hB.1.fintype
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ ⨆ b ∈ (Finset.univ : Finset B), krylovSpace K A b.val := by
      simpa using hw.1
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
      (fun b : B => krylovSpace K A b.val) w).mp hw'
    have hμ' : (∑ b : B, (μ b).val) = w := by simpa using hμ
    have hsum : (∑ b : B, (aeval A f).mulVecLin (μ b).val) = 0 := by
      rw [← map_sum, hμ']
      simpa only [pow_one, Matrix.mulVecLin_apply] using (mem_powerKernel K A f 1 w).mp hw.2
    have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
      (fun b : B => krylovSpace K A b.val)).mp hB.2 Finset.univ
      (fun b => (aeval A f).mulVecLin (μ b).val)
      (fun b _ => aeval_mulVec_mem_krylovSpace K A b.val _ f (μ b).property) hsum
    rw [← hμ']
    apply Submodule.sum_mem
    intro b _
    apply (le_iSup (fun b : B => krylovSpace K A (terminalVector K A f b.val)) b)
    rw [← krylovSpace_inf_powerKernel_eq_terminal K A f hf hm b.val (hker b.property)]
    refine ⟨(μ b).property, ?_⟩
    apply (mem_powerKernel K A f 1 _).mpr
    simpa only [pow_one, Matrix.mulVecLin_apply] using hz b (Finset.mem_univ b)
  · apply iSup_le
    intro b
    rw [← krylovSpace_inf_powerKernel_eq_terminal K A f hf hm b.val (hker b.property)]
    exact inf_le_inf (le_iSup (fun b : B => krylovSpace K A b.val) b) le_rfl

/-- Any nonzero vector in a cyclic space killed by irreducible f generates that space. -/
theorem krylovSpace_eq_of_mem_simple_krylovSpace (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (u w : Fin n → K) (hu0 : u ≠ 0) (hw0 : w ≠ 0)
    (hu : u ∈ powerKernel K A f 1) (hw : w ∈ powerKernel K A f 1)
    (hwu : w ∈ krylovSpace K A u) : krylovSpace K A w = krylovSpace K A u := by
  have hle : krylovSpace K A w ≤ krylovSpace K A u :=
    krylovSpace_le K A w _ hwu (fun v hv => mulVec_mem_krylovSpace K A u v hv)
  have hrank (x : Fin n → K) (hx0 : x ≠ 0) (hx : x ∈ powerKernel K A f 1) :
      vectorRank K A f x = 1 := by
    have h := vectorRank_bounds K A f x hx0 hx
    omega
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_krylovSpace K A f hf hm u hu0 hu (hrank u hu0 hu),
    finrank_krylovSpace K A f hf hm w hw0 hw (hrank w hw0 hw)]

/-- Lemma 15, the disjointness criterion: the new cyclic space meets the old sum
only at zero when its terminal vector lies outside the sum of terminal spaces. -/
theorem krylovSpace_disjoint_of_terminalVector_not_mem (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (v : Fin n → K) (hv : v ∈ powerKernel K A f ℓbar)
    (hnot : terminalVector K A f v ∉ ⨆ b : B, krylovSpace K A (terminalVector K A f b.val)) :
    Disjoint (krylovSpace K A v) (⨆ b : B, krylovSpace K A b.val) := by
  apply Submodule.disjoint_def.mpr
  intro u huv huB
  by_contra hu0
  have hu := krylovSpace_le_powerKernel K A f v ℓbar hv huv
  have hut0 := terminalVector_ne_zero K A f u hu0 hu
  have hut := terminalVector_mem_powerKernel K A f u hu
  have hutv : terminalVector K A f u ∈ krylovSpace K A v := by
    simpa only [map_pow, terminalVector] using aeval_mulVec_mem_krylovSpace K A v u
      (f^(vectorRank K A f u - 1)) huv
  have hutB : terminalVector K A f u ∈ ⨆ b : B, krylovSpace K A b.val := by
    simpa only [map_pow, terminalVector] using aeval_mulVec_mem_iSup_krylovSpace K A
      (fun b : B => b.val) u (f^(vectorRank K A f u - 1)) huB
  have htv : terminalVector K A f u ∈ krylovSpace K A (terminalVector K A f v) := by
    rw [← krylovSpace_inf_powerKernel_eq_terminal K A f hf hm v hv]
    exact ⟨hutv, hut⟩
  have htb : terminalVector K A f u ∈
      ⨆ b : B, krylovSpace K A (terminalVector K A f b.val) := by
    rw [← iSup_krylovSpace_inf_powerKernel K A f hf hm B hB hker]
    exact ⟨hutB, hut⟩
  have hv0 : v ≠ 0 := by
    intro hz
    apply hnot
    simp [hz]
  have he := krylovSpace_eq_of_mem_simple_krylovSpace K A f hf hm
    (terminalVector K A f v) (terminalVector K A f u)
    (terminalVector_ne_zero K A f v hv0 hv) hut0
    (terminalVector_mem_powerKernel K A f v hv) hut htv
  apply hnot
  have hle := krylovSpace_le K A (terminalVector K A f u)
    (⨆ b : B, krylovSpace K A (terminalVector K A f b.val)) htb (fun x hx => by
      simpa only [aeval_X] using aeval_mulVec_mem_iSup_krylovSpace K A
        (fun b : B => terminalVector K A f b.val) x X hx)
  rw [he] at hle
  exact hle (self_mem_krylovSpace K A _)

/-- Lemma 15: adjoining v preserves Jordan–Krylov independence if its terminal
vector is outside the sum of the old terminal Krylov spaces. -/
theorem IsJordanKrylovIndependent.insert_of_terminalVector_not_mem
    (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Fin n → K)) (hB : IsJordanKrylovIndependent K A B)
    (hker : B ⊆ (powerKernel K A f ℓbar : Set (Fin n → K)))
    (v : Fin n → K) (hv : v ∈ powerKernel K A f ℓbar)
    (hnot : terminalVector K A f v ∉ ⨆ b : B, krylovSpace K A (terminalVector K A f b.val)) :
    IsJordanKrylovIndependent K A (insert v B) := by
  classical
  have hd := krylovSpace_disjoint_of_terminalVector_not_mem K A f hf hm B hB hker v hv hnot
  let s := hB.1.toFinset
  have hs : s.SupIndep (fun w => krylovSpace K A w) := by
    apply iSupIndep_comp_coe_iff_supIndep.mp
    change iSupIndep (fun w : (s : Set (Fin n → K)) => krylovSpace K A w.val)
    have hcoe : (s : Set (Fin n → K)) = B := hB.1.coe_toFinset
    rw [hcoe]
    exact hB.2
  have hds : Disjoint (krylovSpace K A v) (s.sup (fun w => krylovSpace K A w)) := by
    simpa only [Finset.sup_eq_iSup, iSup_subtype, s, Set.Finite.mem_toFinset] using hd
  have hi := (hs.insert hds).independent
  refine ⟨hB.1.insert v, ?_⟩
  change iSupIndep (fun w : ((insert v s : Finset (Fin n → K)) : Set (Fin n → K)) =>
    krylovSpace K A w.val) at hi
  have hcoe : ((insert v s : Finset (Fin n → K)) : Set (Fin n → K)) = insert v B := by
    simp [s]
  rw [hcoe] at hi
  exact hi

end SympyProofs.JordanKrylov
