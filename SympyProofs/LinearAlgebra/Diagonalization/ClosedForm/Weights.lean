module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic

/-! # Integer weights for mixing the columns of a spectral projector -/

@[expose] public section
namespace SympyProofs.Diagonalization.Meadow

open Matrix
def weight {n : ℕ} (i j : Fin n) : ℤ := (i.val + 1 : ℤ) ^ j.val

private def laplace : {k : ℕ} → Matrix (Fin k) (Fin k) ℤ → ℤ
  | 0, _ => 1
  | _ + 1, M => ∑ j, (-1) ^ j.val * M 0 j * laplace (M.submatrix Fin.succ j.succAbove)

private theorem laplace_eq {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : laplace M = M.det := by
  induction k with
  | zero => simp [laplace]
  | succ k ih => simp only [laplace, ih, det_succ_row_zero M]

/-- Every square minor of the integer weights is invertible over a characteristic-zero field. -/
def GoodWeights (n : ℕ) : Prop := ∀ (s t : Finset (Fin n)) (h : s.card = t.card),
  (of fun i j : Fin t.card => weight (s.orderEmbOfFin h i) (t.orderEmbOfFin rfl j)).det ≠ 0

private def indices {n : ℕ} (s : Finset (Fin n)) :=
  (List.finRange n).filter (· ∈ s)

private theorem indices_eq {n : ℕ} (s : Finset (Fin n)) : indices s = s.sort := by
  apply ((List.sortedLT_finRange n).pairwise.sublist (List.filter_sublist ..)).sortedLT.eq_of_mem_iff
    s.sortedLT_sort
  simp

private def indexValue {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :=
  ((indices s)[k]?.map Fin.val).getD 0

private theorem indexValue_eq {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k) (i : Fin k) :
    indexValue s i.val = (s.orderEmbOfFin h i).val := by
  rw [indexValue, indices_eq, Finset.orderEmbOfFin_apply,
    List.getElem?_eq_getElem (show i.val < (s.sort (· ≤ ·)).length by simp [h])]
  rfl

private def checkMinor {n : ℕ} (s t : Finset (Fin n)) : Bool :=
  if s.card = t.card then
    laplace (of fun i j : Fin t.card => (indexValue s i.val + 1 : ℤ) ^ indexValue t j.val) != 0
  else true

private theorem good_of_check {n : ℕ} (hc : ∀ s t : Finset (Fin n), checkMinor s t = true) :
    GoodWeights n := by
  intro s t h
  simpa only [checkMinor, h, ↓reduceIte, laplace_eq, indexValue_eq s h, indexValue_eq t rfl,
    bne_iff_ne, weight] using hc s t

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem goodWeights_four : GoodWeights 4 := good_of_check (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem goodWeights_three : GoodWeights 3 := good_of_check (by decide +kernel)

end SympyProofs.Diagonalization.Meadow
