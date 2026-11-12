module

public import SympyProofs.LinearAlgebra.Permanent.Basic

import Mathlib.Logic.Equiv.Fin.Basic

/-! Permanental minors obtained by deleting a row and a column. The remaining
index types may differ, so the permanent is expressed as a sum over bijections
from the remaining columns to the remaining rows. -/

@[expose] public section

namespace Matrix

variable {n : Type*}

/-- The permanent after deleting `row` and `col`, summed over bijections
between the remaining column and row indices. -/
def permanentalMinor {R : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (row col : n) : R :=
  ∑ e : {j : n // j ≠ col} ≃ {i : n // i ≠ row}, ∏ j, A (e j) j

/-- Transposition exchanges the deleted row and column. -/
@[simp]
theorem permanentalMinor_transpose {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (row col : n) :
    permanentalMinor Aᵀ row col = permanentalMinor A col row := by
  unfold permanentalMinor
  rw [← (Equiv.symmEquiv {j : n // j ≠ row} {i : n // i ≠ col}).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  rw [← e.prod_comp]
  simp [transpose_apply]

/-- Any enumerations of the remaining rows and columns give the same minor. -/
theorem permanentalMinor_eq_permanent_submatrix {R m : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n R) (row col : n)
    (er : m ≃ {k : n // k ≠ row}) (ec : m ≃ {k : n // k ≠ col}) :
    permanentalMinor A row col =
      (A.submatrix (fun k => er k) (fun k => ec k)).permanent := by
  rw [permanentalMinor, Matrix.permanent, ← (Equiv.equivCongr ec er).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← ec.prod_comp]
  simp only [Equiv.equivCongr_apply_apply, Equiv.symm_apply_apply, Matrix.submatrix_apply]

/-- For `Fin` indices, deleting a row and a column is expressed by `succAbove`. -/
theorem permanentalMinor_fin {R : Type*} [CommSemiring R] {d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) R) (row col : Fin (d + 1)) :
    permanentalMinor A row col = (A.submatrix row.succAbove col.succAbove).permanent :=
  permanentalMinor_eq_permanent_submatrix A row col
    (finSuccAboveEquiv row) (finSuccAboveEquiv col)

private def extendMinorEquiv [DecidableEq n] (row col : n)
    (e : {k : n // k ≠ col} ≃ {k : n // k ≠ row}) : Equiv.Perm n :=
  (Equiv.optionSubtypeNe col).symm.trans
    (e.optionCongr.trans (Equiv.optionSubtypeNe row))

@[simp] private theorem extendMinorEquiv_self [DecidableEq n] (row col : n)
    (e : {k : n // k ≠ col} ≃ {k : n // k ≠ row}) :
    extendMinorEquiv row col e col = row := by
  simp [extendMinorEquiv]

@[simp] private theorem extendMinorEquiv_apply [DecidableEq n] (row col : n)
    (e : {k : n // k ≠ col} ≃ {k : n // k ≠ row}) (k : n) (hk : k ≠ col) :
    extendMinorEquiv row col e k = e ⟨k, hk⟩ := by
  simp [extendMinorEquiv, Equiv.optionSubtypeNe_symm_of_ne hk]

/-- Restrict a permutation taking `col` to `row` to the remaining indices. -/
private def permutationMinorEquiv [DecidableEq n] (row col : n) :
    {σ : Equiv.Perm n // σ col = row} ≃
      ({k : n // k ≠ col} ≃ {k : n // k ≠ row}) where
  toFun σ := σ.val.subtypeEquiv (by
    intro k
    simp only [← σ.property, ne_eq, Equiv.apply_eq_iff_eq])
  invFun e := ⟨extendMinorEquiv row col e, extendMinorEquiv_self row col e⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro k
    by_cases hk : k = col
    · subst k
      simp [σ.property]
    · rw [extendMinorEquiv_apply row col _ k hk]
      rfl
  right_inv e := by
    apply Equiv.ext
    intro k
    apply Subtype.ext
    exact extendMinorEquiv_apply row col e k k.property

private theorem permanentalMinor_eq_sum {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (row col : n) :
    permanentalMinor A row col =
      ∑ σ : {σ : Equiv.Perm n // σ col = row},
        ∏ k ∈ Finset.univ.erase col, A (σ.val k) k := by
  rw [permanentalMinor, ← (permutationMinorEquiv row col).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  symm
  exact Finset.prod_subtype _ (by simp) _

/-- A basis-column replacement has permanent equal to the corresponding minor. -/
theorem permanentalMinor_eq_permanent_updateCol {R : Type*} [CommSemiring R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (row col : n) :
    permanentalMinor A row col = (A.updateCol col (Pi.single row 1)).permanent := by
  rw [permanentalMinor_eq_sum, permanent_updateCol_eq_sum_perm]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun σ : Equiv.Perm n => σ col = row)
    (Finset.univ.filter (fun σ : Equiv.Perm n => σ col = row)) (by simp)
    (fun σ => ∏ k ∈ Finset.univ.erase col, A (σ k) k)).symm

end Matrix
