import SympyProofs.JordanKrylov.Mathematics.Vec
import SympyProofs.JordanKrylov.Mathematics.BasisExistence
import SympyProofs.JordanKrylov.Mathematics.BasisChainDecomposition
import Mathlib.LinearAlgebra.Eigenspace.Zero
/-! # Characteristic multiplicity bounds for primary kernels

These bounds justify the single-generator early return in Algorithm 2.
The argument uses independent complex chain spaces to bound the total ranks,
then compares the dimensions of a cyclic space and the primary kernel.
-/

namespace SympyProofs.JordanKrylov
open Matrix Polynomial
open scoped DirectSum
/-- Each complex root of an irreducible factor has its factor's multiplicity. -/
theorem rootMultiplicity_map_eq_multiplicity
    (K : Subfield ℂ) (f p : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (hp : p ≠ 0) (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    (p.map K.subtype).rootMultiplicity α = multiplicity f p := by
  have hfin := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
    (Polynomial.degree_pos_of_irreducible hf) hm hp
  obtain ⟨g, heq, hnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hcop : IsCoprime f g := (hf.isCoprime_or_dvd g).resolve_right hnot
  have hg : g ≠ 0 := by intro h; simp [h] at heq; exact hp heq
  have hgm : g.map K.subtype ≠ 0 := Polynomial.map_ne_zero hg
  have hfm : f.map K.subtype ≠ 0 := Polynomial.map_ne_zero hf.ne_zero
  have hgroot : ¬ (g.map K.subtype).IsRoot α := by
    have hc := Polynomial.aeval_ne_zero_of_isCoprime hcop α
    have hz : aeval α f = 0 := hα
    simpa only [IsRoot, eval_map, aeval_def, Subfield.algebraMap_ofSubfield] using hc.resolve_left (not_not.mpr hz)
  have hfr : (f.map K.subtype).rootMultiplicity α = 1 := by
    have hle := rootMultiplicity_le_one_of_separable (p := f.map K.subtype) hf.separable.map α
    have hpos := (rootMultiplicity_pos hfm).mpr (show (f.map K.subtype).IsRoot α from by simpa only [IsRoot, eval_map] using hα)
    omega
  have hpow (j : ℕ) : ((f.map K.subtype)^j).rootMultiplicity α = j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hfm) hfm), ih, hfr]
  conv_lhs => rw [heq, Polynomial.map_mul, Polynomial.map_pow,
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hfm) hgm), hpow,
    rootMultiplicity_eq_zero hgroot, add_zero]
theorem IsJordanKrylovBasis.sum_ranks_le_charpoly_multiplicity
    (K : Subfield ℂ) {n ℓbar : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f) (hm : f.Monic)
    (B : Set (Vec K n)) (hB : IsJordanKrylovBasis K A (powerKernel K A f ℓbar) B)
    [Fintype B] (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    (∑ b : B, vectorRank K A f b.val) ≤ multiplicity f A.charpoly := by
  classical
  let S : B → Submodule ℂ (Fin n → ℂ) := fun b : B => chainSpace K A f b.val (vectorRank K A f b.val) α
  have hind : iSupIndep S :=
    chainSpaces_independent_of_jordanKrylovIndependent K A f B hB.2 α
  let e : (⨁ b : B, S b) ≃ₗ[ℂ] ↥(⨆ b : B, S b) :=
    (LinearEquiv.ofInjective (DirectSum.coeLinearMap S) hind.dfinsupp_lsum_injective).trans
      (LinearEquiv.ofEq _ _ DirectSum.range_coeLinearMap)
  have hdim : Module.finrank ℂ ↥(⨆ b : B, S b) = ∑ b : B, vectorRank K A f b.val := by
    rw [← e.finrank_eq, Module.finrank_directSum]
    apply Finset.sum_congr rfl
    intro b _
    exact finrank_chainSpace K A f hf b.val (hB.1.subset K A _ B b.property) rfl α hα
  have hle : (⨆ b : B, S b) ≤ Module.End.maxGenEigenspace (A.map K.subtype).mulVecLin α := by
    apply iSup_le
    intro b
    exact chainSpace_le_maxGenEigenspace K A f b.val
      (hB.1.subset K A _ B b.property) rfl α hα
  have h := Submodule.finrank_mono hle
  rw [hdim, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_mulVecLin,
    Matrix.charpoly_map, rootMultiplicity_map_eq_multiplicity K f A.charpoly hf hm
      A.charpoly_monic.ne_zero α hα] at h
  exact h

/-- Characteristic multiplicity bounds the dimension of every primary power kernel. -/
theorem finrank_powerKernel_le_charpoly_multiplicity
    (K : Subfield ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic) (ℓbar : ℕ) :
    Module.finrank K (powerKernel K A f ℓbar) ≤ multiplicity f A.charpoly * f.natDegree := by
  classical
  obtain ⟨α, hα⟩ := Complex.exists_root (f := f.map K.subtype) (by
    rw [Polynomial.degree_map]
    exact degree_pos_of_irreducible hf)
  have hroot : f.eval₂ K.subtype α = 0 := by simpa only [IsRoot, eval_map] using hα
  obtain ⟨B, hB⟩ := exists_jordanKrylovBasis_powerKernel K A f hf ℓbar
  let : Fintype B := hB.2.1.fintype
  have hdim := hB.finrank_map K A f hf hm B 0
  change Module.finrank K ((powerKernel K A f ℓbar).map
    (1 : Matrix (Fin n) (Fin n) K).mulVecLin) =
      ∑ b : B, vectorRank K A f b.val * f.natDegree at hdim
  have hmap : (powerKernel K A f ℓbar).map ((1 : Matrix (Fin n) (Fin n) K).mulVecLin) =
      powerKernel K A f ℓbar := by
    have hid : (1 : Matrix (Fin n) (Fin n) K).mulVecLin = LinearMap.id := by ext; simp
    rw [hid, Submodule.map_id]
  rw [hmap, ← Finset.sum_mul] at hdim
  rw [hdim]
  exact Nat.mul_le_mul_right f.natDegree
    (hB.sum_ranks_le_charpoly_multiplicity K A f hf hm B α hroot)

/-- The early-return test in Algorithm 2 is sound: a generator whose rank is the
full characteristic multiplicity already spans the primary kernel. -/
theorem krylovSpace_eq_powerKernel_of_rank_eq_charpoly_multiplicity
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic) (v : Vec K n)
    (hv : v ≠ 0) (hker : v ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f v = multiplicity f A.charpoly) :
    krylovSpace K A v = powerKernel K A f ℓbar := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact krylovSpace_le_powerKernel K A f v ℓbar hker
  · rw [finrank_krylovSpace K A f hf hm v hv hker hrank]
    exact finrank_powerKernel_le_charpoly_multiplicity K A f hf hm ℓbar

theorem singleton_isJordanKrylovBasis_of_rank_eq_charpoly_multiplicity
    (K : Subfield ℂ) {n ℓbar : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : Irreducible f) (hm : f.Monic) (v : Vec K n)
    (hv : v ≠ 0) (hker : v ∈ powerKernel K A f ℓbar)
    (hrank : vectorRank K A f v = multiplicity f A.charpoly) :
    IsJordanKrylovBasis K A (powerKernel K A f ℓbar) {v} := by
  refine ⟨?_, Set.finite_singleton v, iSupIndep_subsingleton _⟩
  change powerKernel K A f ℓbar = ⨆ w ∈ ({v} : Set (Vec K n)), krylovSpace K A w
  simpa using (krylovSpace_eq_powerKernel_of_rank_eq_charpoly_multiplicity
    K A f hf hm v hv hker hrank).symm

end SympyProofs.JordanKrylov
