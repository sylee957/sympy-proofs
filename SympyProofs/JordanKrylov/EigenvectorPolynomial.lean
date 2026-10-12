import SympyProofs.JordanKrylov.Definition
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvector polynomials: nonvanishing, independence, and degree

The three conclusions use explicit hypotheses over a subfield of ℂ.
The characteristic-polynomial factor assumption is needed to obtain w, but
is not needed again once a nonzero w annihilated by f(A) has been supplied.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

private theorem scalar_smul_one {R : Type*} [CommRing R] {n : ℕ} (a : R) :
    Matrix.scalar (Fin n) a = a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar, Matrix.diagonal, h]

private theorem map_aeval_matrix {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (φ : R →+* S) (A : Matrix (Fin n) (Fin n) R) (f : R[X]) :
    (aeval A f).map φ = aeval (A.map φ) (f.map φ) := by
  refine map_aeval_eq_aeval_map (φ := φ)
    (ψ := (φ.mapMatrix : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) S)) ?_ f A
  ext x i j
  by_cases h : i = j <;>
    simp [algebraMap, Matrix.scalar, Matrix.diagonal, Matrix.map_apply, h]

private theorem p_identity (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K) :
    (A.map C - Matrix.scalar (Fin n) X) *ᵥ pCoordinates K A f w =
      (fun i => C (((aeval A f) *ᵥ w) i)) - (fun i => f * C (w i)) := by
  let _ : AddGroup (Polynomial K[X]) := inferInstance
  let ev : Polynomial K[X] →+* Matrix (Fin n) (Fin n) K[X] :=
    eval₂RingHom' (Matrix.scalar (Fin n)) (A.map C)
    (fun a => Matrix.scalar_commute a (fun _ => Commute.all _ _) (A.map C))
  have h := congrArg ev (ψ_identity K f)
  have heval : ev (f.map C) = (aeval A f).map C := by
    rw [map_aeval_matrix]
    rfl
  rw [_root_.map_mul, _root_.map_sub, _root_.map_sub] at h
  have hX : ev X = A.map C := eval₂_X _ _
  have hC (q : K[X]) : ev (C q) = Matrix.scalar (Fin n) q := eval₂_C _ _
  rw [hX, hC, hC] at h
  change (A.map C - Matrix.scalar (Fin n) X) * ev (ψ K f) =
      ev (f.map C) - Matrix.scalar (Fin n) f at h
  rw [heval] at h
  change (A.map C - Matrix.scalar (Fin n) X) *ᵥ
      (ev (ψ K f) *ᵥ (fun i => C (w i))) = _
  rw [Matrix.mulVec_mulVec, h, Matrix.sub_mulVec]
  funext i
  simp [RingHom.map_mulVec, Function.comp_def]

private theorem ψ_swap (K : Subfield ℂ) (f : K[X]) :
    Bivariate.swap (ψ K f) = ψ K f := by
  let _ : AddGroup (Polynomial K[X]) := inferInstance
  have h := congrArg Bivariate.swap (ψ_identity K f)
  simp only [_root_.map_mul, _root_.map_sub, Bivariate.swap_Y,
    Bivariate.swap_map_C, Bivariate.swap_C, Polynomial.map_X] at h
  apply mul_left_cancel₀ (X_sub_C_ne_zero (X : K[X]))
  calc
    (X - C (X : K[X])) * Bivariate.swap (ψ K f) = f.map C - C f := by
      linear_combination -h
    _ = (X - C (X : K[X])) * ψ K f := (ψ_identity K f).symm

private theorem coeff_swap (K : Subfield ℂ) (q : Polynomial K[X]) (i j : ℕ) :
    ((Bivariate.swap q).coeff i).coeff j = (q.coeff j).coeff i := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp [map_add, coeff_add, hq, hr]
  | monomial k a =>
    simp only [Bivariate.swap_monomial, coeff_mul_C, coeff_map, coeff_C_mul,
      coeff_X_pow, coeff_monomial]
    split_ifs <;> simp_all

private theorem ψ_degree (K : Subfield ℂ) (f : K[X]) (hf : 0 < f.degree) :
    (ψ K f).degree < f.degree := by
  unfold ψ
  by_cases hz : f.map C - C f = 0
  · simp only [hz, zero_divByMonic, degree_zero]
    exact lt_trans (by simp) hf
  · apply (degree_divByMonic_lt _ _ hz (by simp)).trans_le
    apply (degree_sub_le _ _).trans
    exact max_le (by simp) ((degree_C_le).trans (le_of_lt hf))

private theorem ψ_coeff_degree (K : Subfield ℂ) (f : K[X]) (hf : 0 < f.degree)
    (j : ℕ) : ((ψ K f).coeff j).degree < f.natDegree := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [← coeff_swap K (ψ K f) m j, ψ_swap]
  have hd : (ψ K f).degree < m :=
    (ψ_degree K f hf).trans_le ((degree_le_natDegree).trans (by exact_mod_cast hm))
  rw [coeff_eq_zero_of_degree_lt hd, coeff_zero]

private theorem p_expansion (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K) (i : Fin n) :
    pCoordinates K A f w i = ∑ j ∈ (ψ K f).support,
      (ψ K f).coeff j * C (((A ^ j) *ᵥ w) i) := by
  classical
  simp only [pCoordinates, eval₂_eq_sum, Polynomial.sum, Matrix.sum_mulVec, Finset.sum_apply,
    ← Matrix.mulVec_mulVec, scalar_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, ← Matrix.map_pow, RingHom.map_mulVec, Function.comp_def]

private theorem p_degree (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : 0 < f.degree)
    (w : Fin n → K) (i : Fin n) : (pCoordinates K A f w i).degree < f.natDegree := by
  classical
  rw [p_expansion, degree_lt_iff_coeff_zero]
  intro m hm
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [coeff_mul_C, (degree_lt_iff_coeff_zero _ _).mp (ψ_coeff_degree K f hf j) m hm,
    zero_mul]

/-- Lemma 1(1): every root of the irreducible f gives a nonzero vector p(α,w). -/
theorem pAt_ne_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (w : Fin n → K) (hw0 : w ≠ 0) (hw : (aeval A f) *ᵥ w = 0)
    (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    pAt K A f α w ≠ 0 := by
  intro hz
  rw [pAt_eq_coordinates] at hz
  have hp : pCoordinates K A f w = 0 := by
    funext i
    have hroot : (pCoordinates K A f w i).aeval α = 0 := congrFun hz i
    have hdiv : f ∣ pCoordinates K A f w i := (hf.dvd_iff_aeval_eq_zero hα).mp hroot
    by_contra hne
    have hle := degree_le_of_dvd hdiv hne
    have hlt := p_degree K A f (degree_pos_of_irreducible hf) w i
    rw [← degree_eq_natDegree hf.ne_zero] at hlt
    exact (not_lt_of_ge hle) hlt
  have h := p_identity K A f w
  rw [hp, hw, Matrix.mulVec_zero] at h
  apply hw0
  funext i
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.sub_apply, map_zero, zero_sub] at hi
  have hzprod : f * C (w i) = 0 := neg_eq_zero.mp hi.symm
  exact C_eq_zero.mp ((mul_eq_zero.mp hzprod).resolve_left hf.ne_zero)

/-- Lemma 1(2): at a root α of f, p(α,w) satisfies the eigenvector equation. -/
theorem pAt_eigenvector_equation (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (w : Fin n → K)
    (hw : (aeval A f) *ᵥ w = 0) (α : ℂ) (hα : f.eval₂ K.subtype α = 0) :
    (A.map K.subtype - α • 1) *ᵥ pAt K A f α w = 0 := by
  let e := eval₂RingHom K.subtype α
  have h := congrArg (fun v : Fin n → K[X] => fun i => e (v i)) (p_identity K A f w)
  rw [hw] at h
  have hmap : (A.map C - Matrix.scalar (Fin n) X).map e = A.map K.subtype - α • 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.map_apply, Matrix.scalar, Matrix.diagonal, hij, e]
  simp only [RingHom.map_mulVec, hmap] at h
  rw [pAt_eq_coordinates]
  have he : e f = 0 := hα
  funext i
  simpa only [Pi.sub_apply, Pi.zero_apply, map_zero, zero_sub, map_neg,
    map_mul, he, zero_mul, neg_zero, Function.comp_def, e, coe_eval₂RingHom] using congrFun h i

/-- Lemma 1(3): the vectors associated to the d = deg f distinct roots
are linearly independent over ℂ. -/
theorem pAt_linearIndependent (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : Irreducible f)
    (w : Fin n → K) (hw0 : w ≠ 0) (hw : (aeval A f) *ᵥ w = 0)
    (α : Fin f.natDegree → ℂ) (hα_distinct : Function.Injective α)
    (hα : ∀ i, f.eval₂ K.subtype (α i) = 0) :
    LinearIndependent ℂ (fun i => pAt K A f (α i) w) := by
  apply Module.End.eigenvectors_linearIndependent' (A.map K.subtype).mulVecLin α hα_distinct
  intro i
  refine ⟨?_, pAt_ne_zero K A f hf w hw0 hw (α i) (hα i)⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  have h := pAt_eigenvector_equation K A f w hw (α i) (hα i)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

/-- For monic f of positive degree d, the coefficient vector of λ^(d-1)
in p(λ,w) is exactly w. No annihilation assumption is needed. -/
private theorem pCoordinates_coeff_pred (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (w : Fin n → K) :
    (fun i => (pCoordinates K A f w i).coeff (f.natDegree - 1)) = w := by
  funext i
  have hdeg (j : Fin n) : (pCoordinates K A f w j).coeff f.natDegree = 0 :=
    coeff_eq_zero_of_degree_lt (p_degree K A f (natDegree_pos_iff_degree_pos.mp hd) w j)
  have hA : ((A.map C *ᵥ pCoordinates K A f w) i).coeff f.natDegree = 0 := by
    simp only [Matrix.mulVec, dotProduct, finsetSum_coeff, Matrix.map_apply, coeff_C_mul,
      hdeg, mul_zero, Finset.sum_const_zero]
  have hX : (X * pCoordinates K A f w i).coeff f.natDegree =
      (pCoordinates K A f w i).coeff (f.natDegree - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    exact coeff_X_mul _ _
  have h := congrArg (fun v : Fin n → K[X] => (v i).coeff f.natDegree)
    (p_identity K A f w)
  rw [Matrix.sub_mulVec, scalar_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coeff_sub, hA, hX,
    coeff_C, ite_eq_right (Nat.ne_of_gt hd), coeff_mul_C, hf.coeff_natDegree,
    one_mul, zero_sub, neg_inj] using h

private theorem p_degree_le_pred (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hd : 0 < f.natDegree)
    (w : Fin n → K) (i : Fin n) :
    (pCoordinates K A f w i).degree ≤ (f.natDegree - 1 : ℕ) := by
  rw [degree_le_iff_coeff_zero]
  intro m hm
  have hm' : f.natDegree - 1 < m := WithBot.coe_lt_coe.mp hm
  exact (degree_lt_iff_coeff_zero _ _).mp
    (p_degree K A f (natDegree_pos_iff_degree_pos.mp hd) w i) m (by omega)

/-- The coefficient of λ^(d-1) in the vector-valued polynomial p is w. -/
theorem p_coeff_pred (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (w : Fin n → K) :
    (p K A f w).coeff (f.natDegree - 1) = w := by
  funext i
  rw [p_coeff_apply]
  exact congrFun (pCoordinates_coeff_pred K A f hf hd w) i

/-- The remark after Lemma 1: p is a polynomial with vector coefficients
of degree d-1, since its coefficient at that exponent is the nonzero vector w. -/
theorem p_degree_eq (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (w : Fin n → K) (hw : w ≠ 0) :
    (p K A f w).degree = (f.natDegree - 1 : ℕ) := by
  classical
  unfold PolynomialModule.degree
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    by_contra hgt
    have hz : (p K A f w).coeff k = 0 := by
      funext i
      rw [p_coeff_apply]
      exact (degree_le_iff_coeff_zero _ _).mp (p_degree_le_pred K A f hd w i)
        k (lt_of_not_ge hgt)
    exact (Finsupp.mem_support_iff.mp hk) hz
  · apply Finset.le_sup
    rw [Finsupp.mem_support_iff, p_coeff_pred K A f hf hd w]
    exact hw

end SympyProofs.JordanKrylov
