import SympyProofs.MoorePenrose.Faddeev.Pseudoinverse
import SympyProofs.MoorePenrose.CauchyBinet
import Mathlib.Analysis.Matrix.PosDef

/-!
# Intrinsic formulas for the Faddeev denominator

The recurrence coefficient is the coefficient of `det (1 + X AᴴA)`.
Generalized Cauchy–Binet identifies it with a sum of squared minors.
-/

namespace SympyProofs.MoorePenrose.Faddeev

open Matrix Polynomial
open scoped ComplexOrder

section Elementary

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Elementary symmetric functions, written without choosing an ordering. -/
def elementary (d : n → R) (k : ℕ) : R :=
  ∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, d i

omit [DecidableEq n] in
theorem spectralPolynomial_coeff_eq_elementary (d : n → R) (k : ℕ) :
    (spectralPolynomial d Finset.univ).coeff k = elementary d k := by
  unfold spectralPolynomial
  rw [Finset.prod_one_add]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    C_mul_X_pow_eq_monomial]
  simp only [Polynomial.finsetSum_coeff, coeff_monomial]
  rw [← Finset.sum_filter]
  congr 1
  ext s
  simp [Finset.mem_powersetCard]

end Elementary

section Hermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The determinant generating polynomial of a Hermitian matrix. -/
theorem det_one_add_X_eq_spectralPolynomial {G : Matrix n n 𝕜} (hG : G.IsHermitian) :
    (1 + (X : 𝕜[X]) • G.map C).det =
      spectralPolynomial (fun i => (hG.eigenvalues i : 𝕜)) Finset.univ := by
  apply Polynomial.funext
  intro x
  change (Polynomial.evalRingHom x) _ = _
  rw [RingHom.map_det]
  have hm : (Polynomial.evalRingHom x).mapMatrix (1 + (X : 𝕜[X]) • G.map C) =
      1 + x • G := by
    ext i j
    change (Polynomial.evalRingHom x)
      ((if i = j then 1 else 0) + X * C (G i j)) =
      (if i = j then 1 else 0) + x * G i j
    rw [map_add, map_mul]
    simp only [coe_evalRingHom, eval_X, eval_C]
    congr 1
    split_ifs <;> simp only [eval_one, eval_zero]
  rw [hm]
  let U := hG.eigenvectorUnitary
  have hconj : 1 + x • G = Unitary.conjStarAlgAut 𝕜 _ U
      (1 + x • diagonal (fun i => (hG.eigenvalues i : 𝕜))) := by
    rw [map_add, map_one, map_smul]
    congr 2
    exact hG.spectral_theorem
  rw [hconj, Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  rw [← diagonal_one, ← diagonal_smul, diagonal_add, Matrix.det_diagonal]
  simp only [spectralPolynomial, Polynomial.eval_prod, eval_add, eval_one,
    eval_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem coeff_eq_det_one_add_X_coeff {G : Matrix n n 𝕜} (hG : G.IsHermitian) (k : ℕ) :
    coeff G k = (1 + (X : 𝕜[X]) • G.map C).det.coeff k := by
  rw [det_one_add_X_eq_spectralPolynomial hG]
  exact congrArg Prod.fst (state_spectral hG k)

end Hermitian

section Denominator

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- The recurrence denominator is the coefficient of the Gram determinant polynomial. -/
theorem denominator_eq_det_coeff (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k = (1 + (X : 𝕜[X]) • (Aᴴ * A).map C).det.coeff k :=
  coeff_eq_det_one_add_X_coeff (Matrix.isHermitian_conjTranspose_mul_self A) k

end Denominator

section SubmatrixDenominator

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]

/-- Generalized Cauchy–Binet using mathlib's submatrix determinant directly.
Increasing embeddings count each pair of `k`-element row and column subsets once. -/
theorem denominator_eq_sum_sq_det (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k =
      ((∑ rows : Fin k ↪o m, ∑ cols : Fin k ↪o n,
        ‖(A.submatrix rows cols).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Finset.sum_comm, denominator_eq_det_coeff, Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    RCLike.ofReal_sum]
  rw [Finset.sum_subtype _ (by simp : ∀ t : Finset n,
    t ∈ Finset.univ.powersetCard k ↔ t.card = k)]
  refine Fintype.sum_equiv (Set.powersetCard.ofFinEmbEquiv (n := k) (I := n)).symm
    _ _ fun t => ?_
  rw [← Matrix.det_submatrix_equiv_self (t.val.orderIsoOfFin t.property).toEquiv]
  change ((Aᴴ * A).submatrix (t.val.orderEmbOfFin t.property)
    (t.val.orderEmbOfFin t.property)).det = _
  have hGram : (Aᴴ * A).submatrix (t.val.orderEmbOfFin t.property)
      (t.val.orderEmbOfFin t.property) =
      (A.submatrix id (t.val.orderEmbOfFin t.property))ᴴ *
        A.submatrix id (t.val.orderEmbOfFin t.property) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  rw [hGram, det_gram_eq_sum_sq_submatrix_det]
  rfl

/-- The denominator vanishes exactly when all the selected submatrix determinants vanish. -/
theorem denominator_eq_zero_iff_all_submatrix_det_zero (A : Matrix m n 𝕜) (k : ℕ) :
    denominator A k = 0 ↔
      ∀ (rows : Fin k ↪o m) (cols : Fin k ↪o n),
        (A.submatrix rows cols).det = 0 := by
  rw [denominator_eq_sum_sq_det, RCLike.ofReal_eq_zero]
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => Finset.sum_nonneg fun s _ => sq_nonneg _)]
  simp_rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => sq_nonneg _),
    sq_eq_zero_iff, norm_eq_zero]
  simp

end SubmatrixDenominator

end SympyProofs.MoorePenrose.Faddeev
