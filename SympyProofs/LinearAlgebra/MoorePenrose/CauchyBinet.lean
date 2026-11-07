import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.Hom.PowersetCard

/-!
# Rectangular Cauchy–Binet

The proof compares coefficients in the Weinstein–Aronszajn identity
`det (1 + X AB) = det (1 + X BA)`. Increasing embeddings count each selected
subset once, and every determinant uses mathlib's `Matrix.submatrix` directly.
The matrix index types remain arbitrary finite linear orders.
-/

namespace SympyProofs.MoorePenrose

open Matrix Polynomial

section CommutativeRing

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem det_one_add_X_mul_comm (A : Matrix m n R) (B : Matrix n m R) :
    (1 + (X : R[X]) • (A * B).map C).det =
      (1 + (X : R[X]) • (B * A).map C).det := by
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] using
    Matrix.det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C)

end CommutativeRing

section SubmatrixDeterminants

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]

/-- Rectangular Cauchy–Binet using the determinants of selected submatrices. -/
theorem det_mul_eq_sum_submatrix_det (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).det = ∑ selected : n ↪o m,
      (A.submatrix id selected).det * (B.submatrix selected id).det := by
  have htop : (1 + (X : R[X]) • (A * B).map C).det.coeff (Fintype.card n) =
      (A * B).det := by
    simpa [Matrix.map_one, add_comm] using
      Polynomial.coeff_det_X_add_C_card (A * B) 1
  rw [← htop, det_one_add_X_mul_comm, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  rw [Finset.sum_subtype _ (by simp : ∀ s : Finset m,
    s ∈ Finset.univ.powersetCard (Fintype.card n) ↔ s.card = Fintype.card n)]
  let e : Fin (Fintype.card n) ≃o n := Fintype.orderIsoFinOfCardEq n rfl
  let selections : (n ↪o m) ≃ Set.powersetCard m (Fintype.card n) :=
    (e.symm.orderEmbeddingCongr (OrderIso.refl m)).trans Set.powersetCard.ofFinEmbEquiv
  refine Fintype.sum_equiv selections.symm _ _ fun s => ?_
  rw [← Matrix.det_submatrix_equiv_self
    (e.symm.trans (s.val.orderIsoOfFin s.property)).toEquiv]
  change ((B * A).submatrix (selections.symm s) (selections.symm s)).det = _
  rw [← Matrix.submatrix_mul_equiv B A (selections.symm s)
    (Equiv.refl n) (selections.symm s), Matrix.det_mul, mul_comm]
  rfl

end SubmatrixDeterminants

section Gram

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]

/-- The Gram determinant is the sum of squared norms of selected submatrix determinants. -/
theorem det_gram_eq_sum_sq_submatrix_det (A : Matrix m n 𝕜) :
    (Aᴴ * A).det =
      ((∑ rows : n ↪o m, ‖(A.submatrix rows id).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_submatrix_det]
  simp only [RCLike.ofReal_sum, RCLike.ofReal_pow]
  refine Finset.sum_congr rfl fun rows _ => ?_
  have hconj : Aᴴ.submatrix id rows = (A.submatrix rows id)ᴴ := rfl
  rw [hconj, Matrix.det_conjTranspose]
  exact RCLike.conj_mul _

end Gram

end SympyProofs.MoorePenrose
