module

public import SympyProofs.LinearAlgebra.Diagonalization.ClosedForm.Meadow
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Complex.Basic

/-! # Spectral projectors from a fixed tuple of eigenvalues with multiplicity -/

@[expose] public section
noncomputable section
namespace SympyProofs.Diagonalization.Meadow
open Matrix Polynomial
variable {K : Type*} [Field K] {n : ℕ}

/-- A repeated label contributes an identity factor because the inverse of zero is zero. -/
def projector (A : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (x : K) : Matrix (Fin n) (Fin n) K :=
  (List.ofFn fun j => 1 + (x - d j)⁻¹ • (A - x • 1)).prod

theorem mem_labels_iff (d : Fin n → K) (x : K) :
    x ∈ List.ofFn d ↔ ∏ j, (x - d j) = 0 := by
  simp only [List.mem_ofFn, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero]
  exact exists_congr fun _ => eq_comm

def spectrum (d : Fin n → K) : Multiset K := Finset.univ.val.map d

theorem roots_diagonal (d : Fin n → K) : (diagonal d).charpoly.roots = spectrum d := by
  rw [charpoly_diagonal, ← roots_multiset_prod_X_sub_C (spectrum d)]
  simp [spectrum, Finset.prod, Function.comp_def]

theorem real_spectrum {A P : Matrix (Fin n) (Fin n) ℝ} {e : Fin n → ℝ} {z : Fin n → ℂ}
    (h : IsDiagonalization A P e) (hz : (A.map Complex.ofRealHom).charpoly = (diagonal z).charpoly) :
    spectrum (fun i => (z i).re) = spectrum e := by
  have hm : (diagonal (fun i => (e i : ℂ))).charpoly = (diagonal z).charpoly := by
    rw [← hz, charpoly_map, charpoly_eq h, ← charpoly_map]
    congr 1
    ext i j
    by_cases hh : i = j <;> simp [hh]
  have hs := congrArg (Multiset.map Complex.re) (congrArg Polynomial.roots hm.symm)
  simpa [roots_diagonal, spectrum, Multiset.map_map, Function.comp_def] using hs

variable [DecidableEq K]

omit [Field K] in
theorem fiber_card {d e : Fin n → K} (h : spectrum d = spectrum e) (x : K) :
    (Finset.univ.filter (fun j => x = d j)).card =
      (Finset.univ.filter (fun j => x = e j)).card := by
  simpa only [spectrum, Multiset.count_map, Finset.card, Finset.filter_val] using
    congrArg (Multiset.count x) h

theorem projector_mul_basis {A Q : Matrix (Fin n) (Fin n) K}
    {d e : Fin n → K} (h : IsDiagonalization A Q e)
    (hs : spectrum d = spectrum e) (x : K) :
    projector A d x * Q = Q * diagonal (fun i => if x = e i then 1 else 0) := by
  let f := fun j => 1 + C (x - d j)⁻¹ * (X - C x)
  have hp : aeval A (∏ j, f j) = projector A d x := by
    rw [← Fin.prod_ofFn, map_list_prod, List.map_ofFn]
    simp [projector, f, Algebra.algebraMap_eq_smul_one, Function.comp_def]
  rw [← hp, aeval_mul_basis ((isDiagonalization_iff ..).mp h).2]
  congr 2
  funext i
  rw [eval_prod]
  by_cases hi : x = e i
  · simp [f, hi]
  · simp only [hi, ↓reduceIte]
    have hm : e i ∈ spectrum d := hs ▸ Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [f, hj]
    field_simp [sub_ne_zero.mpr hi]
    ring

theorem projector_rank {A Q : Matrix (Fin n) (Fin n) K} {d e : Fin n → K}
    (h : IsDiagonalization A Q e)
    (hs : spectrum d = spectrum e) (x : K) :
    (projector A d x).rank = (Finset.univ.filter (fun j => x = d j)).card := by
  rw [← rank_mul_eq_left_of_isUnit_det Q _ (isUnit_iff_ne_zero.mpr h.1),
    projector_mul_basis h hs, rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr h.1),
    rank_diagonal, fiber_card hs, Fintype.card_subtype]
  congr 1
  ext i
  by_cases hi : x = e i <;> simp [hi]

theorem projector_eigen {A Q : Matrix (Fin n) (Fin n) K}
    {d e : Fin n → K} (h : IsDiagonalization A Q e)
    (hs : spectrum d = spectrum e) (x : K) :
    A * projector A d x = x • projector A d x := by
  let b := fun i => if x = e i then (1 : K) else 0
  have hb : diagonal e * diagonal b = x • diagonal b := by
    rw [diagonal_mul_diagonal, ← diagonal_smul]
    congr 1
    funext i
    by_cases hi : x = e i <;> simp [b, hi]
  have he := projector_mul_basis h hs x
  change _ = Q * diagonal b at he
  apply ((Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr h.1)).mul_left_inj.mp
  rw [mul_assoc, he, ← mul_assoc A, ((isDiagonalization_iff ..).mp h).2, mul_assoc, hb,
    Matrix.mul_smul, Matrix.smul_mul, he]

end SympyProofs.Diagonalization.Meadow
