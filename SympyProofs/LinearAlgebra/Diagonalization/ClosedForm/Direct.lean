module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Elimination
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Projectors
public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Weights
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Direct eigenbases from spectral projectors and fixed column weights -/

@[expose] public section
noncomputable section
namespace SympyProofs.Diagonalization.Meadow
open Matrix
variable {n : ℕ} {K : Type*} [Field K]

/-- Weight the j-th residual column by (i+1)^j, using zero-based indices. -/
def blend (M : Matrix (Fin n) (Fin n) K) (i : Fin n) : Fin n → K :=
  ∑ j, (weight i j : K) • reduce M.col j

/-- Column i is a fixed linear combination in the eigenspace of the i-th label. -/
def basisMatrix (A : Matrix (Fin n) (Fin n) K) (d : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  of fun k i => blend (projector A d (d i)) i k

private theorem blend_mem (M : Matrix (Fin n) (Fin n) K) (i : Fin n) (S : Submodule K (Fin n → K))
    (h : ∀ j, M.col j ∈ S) : blend M i ∈ S :=
  S.sum_mem fun j _ => S.smul_mem _ ((reduce_mem M.col S).mpr h j)

private theorem row_mul_mem {m : ℕ} (B : Matrix (Fin m) (Fin m) K) (U : Matrix (Fin m) (Fin n) K)
    (S : Submodule K (Fin n → K)) (h : ∀ j, U.row j ∈ S) (i : Fin m) : (B * U).row i ∈ S := by
  have he : (B * U).row i = ∑ j, B i j • U.row j := by
    ext k
    simp [Matrix.mul_apply, Matrix.row]
  rw [he]
  exact S.sum_mem fun j _ => S.smul_mem _ (h j)

/-- Any rank-many selected blends span every column, since the corresponding minor is a unit. -/
private theorem recover [CharZero K] (good : GoodWeights n)
    (M : Matrix (Fin n) (Fin n) K) (t : Finset (Fin n))
    (ht : t.card = M.rank) (S : Submodule K (Fin n → K))
    (hm : ∀ j ∈ t, blend M j ∈ S) : ∀ j, M.col j ∈ S := by
  classical
  let u := reduce M.col
  let s := Finset.univ.filter fun j => u j ≠ 0
  have hts : t.card = s.card := ht.trans (support_card M).symm
  let a := t.orderEmbOfFin hts
  let b := s.orderEmbOfFin rfl
  let W : Matrix (Fin s.card) (Fin s.card) ℤ := of fun i j => weight (a i) (b j)
  let B := W.map (Int.castRingHom K)
  let U : Matrix (Fin s.card) (Fin n) K := of fun j => u (b j)
  have hd : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, show B.det = (W.det : K) from ((Int.castRingHom K).map_det W).symm]
    exact_mod_cast good t s hts
  have hout (j) (hj : j ∉ s) : u j = 0 := by simpa [s] using hj
  have hmix (i) : (B * U).row i = blend M (a i) := by
    unfold blend
    rw [sum_indices s _ (fun j hj => by simp [show reduce M.col j = 0 from hout j hj])]
    ext k
    simp [B, W, U, Matrix.mul_apply, Matrix.row, b, u]
  have hU (j) : U.row j ∈ S := by
    rw [← B.nonsing_inv_mul_cancel_left U hd]
    exact row_mul_mem _ _ _ (fun i => hmix i ▸ hm (a i) (t.orderEmbOfFin_mem _ _)) j
  apply (reduce_mem M.col S).mp
  intro j
  by_cases hj : j ∈ s
  · have hj' : j ∈ Set.range b := (s.range_orderEmbOfFin rfl).symm ▸ hj
    obtain ⟨k, hk⟩ := hj'
    exact hk ▸ hU k
  · change u j ∈ S
    rw [hout _ hj]
    exact S.zero_mem

theorem basisMatrix_correct [CharZero K] {A Q : Matrix (Fin n) (Fin n) K} {d e : Fin n → K}
    (good : GoodWeights n) (h : IsDiagonalization A Q e) (hs : spectrum d = spectrum e) :
    IsDiagonalization A (basisMatrix A d) d := by
  classical
  let P := basisMatrix A d
  let S := LinearMap.range P.mulVecLin
  have hP (i) : P.col i ∈ S := by
    change P.col i ∈ LinearMap.range P.mulVecLin
    rw [range_mulVecLin]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hproj (x : K) : ∀ j, (projector A d x).col j ∈ S := by
    apply recover good _ (Finset.univ.filter fun j => x = d j) (projector_rank h hs x).symm
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
    exact hP j
  have hQ (i) : Q.col i ∈ S := by
    let E := projector A d (e i)
    have he : (E * Q).col i = Q.col i := by
      ext k
      simp [E, projector_mul_basis h hs, Matrix.col]
    rw [← he, col_mul_eq_mulVec_col]
    have hr : LinearMap.range E.mulVecLin ≤ S := by
      rw [range_mulVecLin, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hproj (e i) j
    exact hr ⟨_, rfl⟩
  have htop : LinearMap.range Q.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr
    (mulVec_surjective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h.1)))
  have hS : S = ⊤ := by
    apply top_unique
    rw [← htop, range_mulVecLin, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hQ i
  apply (isDiagonalization_iff ..).mpr
  constructor
  · exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det P).mp
      (mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp hS)))
  · ext k i
    let x := d i
    let E := projector A d x
    let V := Module.End.eigenspace A.mulVecLin x
    have he (j) : E.col j ∈ V := by
      apply Module.End.mem_eigenspace_iff.mpr
      change (A * E).col j = x • E.col j
      rw [projector_eigen h hs x]
      rfl
    have hv := Module.End.mem_eigenspace_iff.mp (blend_mem E i V he)
    have hv' : (A * P).col i = x • P.col i := hv
    simpa [Matrix.col, Matrix.mul_diagonal, mul_comm] using congrFun hv' k

end SympyProofs.Diagonalization.Meadow
