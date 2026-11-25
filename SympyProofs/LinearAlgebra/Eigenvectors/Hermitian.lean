module

public import Mathlib.Analysis.Matrix.Spectrum
public import SympyProofs.LinearAlgebra.Diagonalization.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Orthogonality of Hermitian eigenvectors and eigenbases -/

@[expose] public section

namespace SympyProofs.Diagonalization

open Matrix WithLp
open scoped Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- Two eigenvectors of a Hermitian matrix with different eigenvalues are orthogonal.
For a Gram matrix use `isHermitian_conjTranspose_mul_self` or `isHermitian_mul_conjTranspose_self`. -/
theorem eigenvectors_orthogonal_of_ne {G : Matrix n n 𝕜} (hG : G.IsHermitian)
    {μ ν : 𝕜} (hne : μ ≠ ν) {v w : n → 𝕜}
    (hv : G *ᵥ v = μ • v) (hw : G *ᵥ w = ν • w) : star v ⬝ᵥ w = 0 := by
  classical
  have mem {c : 𝕜} {u : n → 𝕜} (hu : G *ᵥ u = c • u) :
      toLp 2 u ∈ Module.End.eigenspace G.toEuclideanLin c := by
    apply Module.End.mem_eigenspace_iff.mpr
    exact (ofLp_injective 2) hu
  rw [dotProduct_comm]
  exact (isSymmetric_toEuclideanLin_iff.mpr hG).orthogonalFamily_eigenspaces hne
    ⟨_, mem hv⟩ ⟨_, mem hw⟩

/-- In any diagonalizing matrix, columns with different diagonal labels are orthogonal. -/
theorem IsDiagonalization.columns_orthogonal_of_ne {k : ℕ} {G P : Matrix (Fin k) (Fin k) 𝕜}
    {d : Fin k → 𝕜} (h : IsDiagonalization G P d) (hG : G.IsHermitian)
    {i j : Fin k} (hne : d i ≠ d j) : star (P.col i) ⬝ᵥ P.col j = 0 := by
  have he (r : Fin k) : G *ᵥ P.col r = d r • P.col r := by
    rw [← col_mul_eq_mulVec_col, ((isDiagonalization_iff ..).mp h).2]
    ext s
    simp [Matrix.col, mul_comm]
  exact eigenvectors_orthogonal_of_ne hG hne (he i) (he j)

/-- Every eigenbasis with the given diagonal has pairwise orthogonal columns exactly
when the diagonal entries are distinct. With a repeated label, adding one corresponding
basis column to the other still gives an eigenbasis. -/
theorem all_eigenbases_orthogonal_iff_injective {k : ℕ} {G P : Matrix (Fin k) (Fin k) 𝕜}
    {d : Fin k → 𝕜} (hG : G.IsHermitian) (h : IsDiagonalization G P d) :
    (∀ Q, IsDiagonalization G Q d → Pairwise (fun i j => star (Q.col i) ⬝ᵥ Q.col j = 0)) ↔
      Function.Injective d := by
  constructor
  · intro hall i j hd
    by_contra hij
    let T := transvection i j (1 : 𝕜)
    have hcomm : diagonal d * T = T * diagonal d := by
      ext a b
      rw [diagonal_mul, mul_diagonal]
      by_cases hab : a = b
      · simp [hab, mul_comm]
      · by_cases hs : i = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := hs
          rw [hd, mul_comm]
        · simp [T, transvection, hab, hs]
    have hQ : IsDiagonalization G (P * T) d := by
      apply (isDiagonalization_iff ..).mpr
      refine ⟨by simpa [T, det_mul, det_transvection_of_ne i j hij] using h.1, ?_⟩
      rw [← mul_assoc, ((isDiagonalization_iff ..).mp h).2, mul_assoc, hcomm, mul_assoc]
    have hi : (P * T).col i = P.col i := by ext a; simp [T, col, hij]
    have hj : (P * T).col j = P.col j + P.col i := by ext a; simp [T, col]
    have hzero : star ((P * T).col i) ⬝ᵥ (P * T).col j = 0 := hall _ hQ hij
    have horth : star (P.col i) ⬝ᵥ P.col j = 0 := hall P h hij
    rw [hi, hj, dotProduct_add, horth, zero_add, dotProduct_comm] at hzero
    change inner 𝕜 (toLp 2 (P.col i)) (toLp 2 (P.col i)) = 0 at hzero
    have hcol := inner_self_eq_zero.mp hzero
    exact (linearIndependent_cols_of_det_ne_zero h.1).ne_zero i (congrArg ofLp hcol)
  · exact fun hd Q hQ _ _ hij => hQ.columns_orthogonal_of_ne hG (hd.ne hij)

end SympyProofs.Diagonalization
