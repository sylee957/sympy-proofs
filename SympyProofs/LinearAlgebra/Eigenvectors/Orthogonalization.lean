module

public import SympyProofs.LinearAlgebra.Eigenvectors.Hermitian
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # Orthogonalizing a Hermitian eigenbasis by squared lengths -/

@[expose] public section

noncomputable section
namespace SympyProofs.Diagonalization

open Matrix WithLp InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Unnormalized Gram–Schmidt. Each projection divides by the Hermitian squared length. -/
def orthogonalizedColumn (P : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) : EuclideanSpace 𝕜 (Fin n) :=
  let v := toLp 2 (P.col i)
  v - ∑ j : Finset.Iio i,
    let q := orthogonalizedColumn P j
    (inner 𝕜 q v / inner 𝕜 q q) • q
termination_by i.val
decreasing_by exact (show (j : Fin n) < i from Finset.mem_Iio.mp j.2)

private theorem column_eq_gramSchmidt (P : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    orthogonalizedColumn P i = gramSchmidt 𝕜 (fun j => toLp 2 (P.col j)) i := by
  induction i using (show WellFounded (fun a b : Fin n => a < b) from wellFounded_lt).induction with
  | h i ih =>
    let v := fun j => toLp 2 (P.col j)
    have h := gramSchmidt_def'' 𝕜 v i
    rw [orthogonalizedColumn, sub_eq_iff_eq_add]
    have he (j : Finset.Iio i) : orthogonalizedColumn P j = gramSchmidt 𝕜 v j :=
      ih j (Finset.mem_Iio.mp j.2)
    rw [← Finset.sum_coe_sort] at h
    simpa only [he, inner_self_eq_norm_sq_to_K, v] using h

/-- Assemble the orthogonal columns in the original order. -/
def orthogonalizeColumns (P : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  of fun k i => orthogonalizedColumn P i k

theorem orthogonalizeColumns_orthogonal (P : Matrix (Fin n) (Fin n) 𝕜) {i j : Fin n} (h : i ≠ j) :
    star ((orthogonalizeColumns P).col i) ⬝ᵥ (orthogonalizeColumns P).col j = 0 := by
  rw [dotProduct_comm]
  change inner 𝕜 (orthogonalizedColumn P i) (orthogonalizedColumn P j) = 0
  simpa only [column_eq_gramSchmidt] using
    gramSchmidt_orthogonal 𝕜 (fun k => toLp 2 (P.col k)) h

private theorem orthogonalizeColumns_det_ne_zero {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.det ≠ 0) :
    (orthogonalizeColumns P).det ≠ 0 := by
  let e := WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)
  have hv := (linearIndependent_cols_of_det_ne_zero hP).map' e.symm.toLinearMap e.symm.ker
  have hq := (gramSchmidt_linearIndependent hv).map' e.toLinearMap e.ker
  apply isUnit_iff_ne_zero.mp
  apply (isUnit_iff_isUnit_det _).mp
  apply linearIndependent_col_iff_isUnit.mp
  convert hq using 1
  funext i
  exact congrArg ofLp (column_eq_gramSchmidt P i)

/-- Orthogonalization preserves each eigenvalue, even when its columns are interleaved
with columns from other eigenspaces. -/
theorem IsDiagonalization.orthogonalizeColumns {G P : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜}
    (h : IsDiagonalization G P d) (hG : G.IsHermitian) :
    IsDiagonalization G (orthogonalizeColumns P) d := by
  let v := fun i => toLp 2 (P.col i)
  let E := fun i => Module.End.eigenspace G.toEuclideanLin (d i)
  have hv (i) : v i ∈ E i := by
    apply Module.End.mem_eigenspace_iff.mpr
    apply ofLp_injective 2
    change (G * P).col i = d i • P.col i
    rw [((isDiagonalization_iff ..).mp h).2]
    ext k
    simp [col, mul_comm]
  have hq (i) : orthogonalizedColumn P i ∈ E i := by
    induction i using (show WellFounded (fun a b : Fin n => a < b) from wellFounded_lt).induction with
    | h i ih =>
      rw [orthogonalizedColumn]
      refine (E i).sub_mem (hv i) ((E i).sum_mem fun j _ => ?_)
      have hj := ih j.val (Finset.mem_Iio.mp j.2)
      by_cases hd : d j = d i
      · exact (E i).smul_mem _ ((show E j = E i by dsimp only [E]; rw [hd]) ▸ hj)
      · have hz : inner 𝕜 (orthogonalizedColumn P j) (v i) = 0 :=
          (isSymmetric_toEuclideanLin_iff.mpr hG).orthogonalFamily_eigenspaces hd ⟨_, hj⟩ ⟨_, hv i⟩
        change inner 𝕜 (orthogonalizedColumn P j) (toLp 2 (P.col i)) = 0 at hz
        simp only [hz, zero_div, zero_smul, Submodule.zero_mem]
  refine (isDiagonalization_iff ..).mpr ⟨orthogonalizeColumns_det_ne_zero h.1, ?_⟩
  ext k i
  have he := congrArg (fun v : EuclideanSpace 𝕜 (Fin n) => v k) (Module.End.mem_eigenspace_iff.mp (hq i))
  rw [mul_diagonal, mul_comm]
  exact he

/-- For an orthogonal basis, the diagonal inverse squared lengths convert Qᴴ into Q⁻¹. -/
theorem inv_of_orthogonal_columns {Q : Matrix (Fin n) (Fin n) 𝕜} (hQ : Q.det ≠ 0)
    (ho : Pairwise fun i j => star (Q.col i) ⬝ᵥ Q.col j = 0) :
    Q⁻¹ = diagonal (fun i => (star (Q.col i) ⬝ᵥ Q.col i)⁻¹) * Qᴴ := by
  apply Matrix.inv_eq_left_inv
  rw [mul_assoc]
  ext i j
  rw [diagonal_mul]
  change (star (Q.col i) ⬝ᵥ Q.col i)⁻¹ * (star (Q.col i) ⬝ᵥ Q.col j) = _
  by_cases hij : i = j
  · subst j
    have hn : star (Q.col i) ⬝ᵥ Q.col i ≠ 0 := by
      rw [dotProduct_comm]
      change inner 𝕜 (toLp 2 (Q.col i)) (toLp 2 (Q.col i)) ≠ 0
      exact inner_self_ne_zero.mpr fun hz =>
        (linearIndependent_cols_of_det_ne_zero hQ).ne_zero i (congrArg ofLp hz)
    simp [hn]
  · simp [ho hij, hij]

end SympyProofs.Diagonalization
