module

public import SympyProofs.LinearAlgebra.MatrixTrace.MatrixUnit
public import Mathlib.Basic.Real.Sign

import Mathlib.Tactic.NormNum

/-! Integer-indexed matrix units and bounds-preserving trace formulas.

`matrixUnitInt m n i j` is a matrix unit when both integer indices are valid,
and the zero matrix otherwise. Its trace keeps the bounds explicit even when
`i = j`. An integer-sign formula works over any ring: division by two takes place
in `ℤ` before casting to the coefficient ring. The real-sign formula is a corollary.
-/

@[expose] public section

namespace Matrix

variable {R : Type*}

/-- A matrix unit with integer indices, extended by zero outside the matrix. -/
def matrixUnitInt [Zero R] [One R] (m n : ℕ) (i j : ℤ) : Matrix (Fin m) (Fin n) R :=
  if hi : 0 ≤ i ∧ i < m then
    if hj : 0 ≤ j ∧ j < n then
      single ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩ 1
    else 0
  else 0

/-- Valid finite indices recover the usual matrix unit. -/
@[simp]
theorem matrixUnitInt_fin [Zero R] [One R] {m n : ℕ} (i : Fin m) (j : Fin n) :
    matrixUnitInt m n (i.val : ℤ) (j.val : ℤ) = (single i j 1 : Matrix _ _ R) := by
  simp [matrixUnitInt, i.is_lt, j.is_lt]

/-- An invalid row or column index gives the zero matrix. -/
theorem matrixUnitInt_eq_zero [Zero R] [One R] (m n : ℕ) (i j : ℤ)
    (h : ¬ (0 ≤ i ∧ i < m ∧ 0 ≤ j ∧ j < n)) :
    matrixUnitInt m n i j = (0 : Matrix _ _ R) := by
  by_cases hi : 0 ≤ i ∧ i < m
  · have hj : ¬ (0 ≤ j ∧ j < n) := by omega
    simp [matrixUnitInt, hi, hj]
  · simp [matrixUnitInt, hi]

/-- The trace is one exactly when the integer indices coincide inside the range.
This includes negative indices and the empty `0 × 0` matrix. -/
theorem trace_matrixUnitInt [AddCommMonoidWithOne R] (n : ℕ) (i j : ℤ) :
    trace (matrixUnitInt n n i j : Matrix _ _ R) =
      if i = j ∧ 0 ≤ i ∧ i < n then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    by_cases hi : 0 ≤ i ∧ i < n <;> simp [matrixUnitInt, hi]
  · by_cases hi : 0 ≤ i ∧ i < n
    · by_cases hj : 0 ≤ j ∧ j < n
      · have hne : (⟨i.toNat, by omega⟩ : Fin n) ≠ ⟨j.toNat, by omega⟩ := by
          intro heq
          have := congrArg Fin.val heq
          change i.toNat = j.toNat at this
          omega
        simp [matrixUnitInt, hi, hj, hij, hne]
      · simp [matrixUnitInt, hj, hij]
    · simp [matrixUnitInt, hi, hij]

private theorem intSign_sub_eq_two_mul_indicator (n : ℕ) (i : ℤ) :
    Int.sign (2 * i + 1) - Int.sign (2 * i - 2 * (n : ℤ) + 1) =
      2 * (if 0 ≤ i ∧ i < n then 1 else 0) := by
  by_cases hi : 0 ≤ i
  · have hs₁ := Int.sign_eq_one_of_pos (show (0 : ℤ) < 2 * i + 1 by omega)
    by_cases hn : i < n
    · have hs₂ := Int.sign_eq_neg_one_of_neg (show 2 * i - 2 * (n : ℤ) + 1 < 0 by omega)
      norm_num [hi, hn, hs₁, hs₂]
    · have hs₂ := Int.sign_eq_one_of_pos (show (0 : ℤ) < 2 * i - 2 * (n : ℤ) + 1 by omega)
      simp [hi, hn, hs₁, hs₂]
  · have hs₁ := Int.sign_eq_neg_one_of_neg (show 2 * i + 1 < (0 : ℤ) by omega)
    have hs₂ := Int.sign_eq_neg_one_of_neg (show 2 * i - 2 * (n : ℤ) + 1 < 0 by omega)
    simp [hi, hs₁, hs₂]

/-- Kronecker delta times an integer-sign range indicator over any coefficient ring.
The sign difference is zero or two; division takes place in `ℤ` before casting,
so the coefficient ring needs neither an ordering nor an inverse of two.
The odd arguments avoid zero at either boundary, including when `n = 0`. -/
theorem trace_matrixUnitInt_eq_intSign [Ring R] (n : ℕ) (i j : ℤ) :
    trace (matrixUnitInt n n i j : Matrix _ _ R) =
      (if i = j then (1 : R) else 0) *
        (((Int.sign (2 * i + 1) - Int.sign (2 * i - 2 * (n : ℤ) + 1)) / 2 : ℤ) : R) := by
  rw [trace_matrixUnitInt, intSign_sub_eq_two_mul_indicator]
  by_cases hij : i = j
  · subst j
    by_cases hi : 0 ≤ i ∧ i < n <;> simp [hi]
  · simp [hij]

/-- The real-sign version of `trace_matrixUnitInt_eq_intSign`.
The bounds remain present when `i = j`. -/
theorem trace_matrixUnitInt_eq_sign (n : ℕ) (i j : ℤ) :
    trace (matrixUnitInt n n i j : Matrix _ _ ℝ) =
      (if i = j then (1 : ℝ) else 0) *
        ((Real.sign (2 * (i : ℝ) + 1) - Real.sign (2 * (i : ℝ) - 2 * n + 1)) / 2) := by
  rw [trace_matrixUnitInt_eq_intSign]
  congr 1
  have hs : Real.sign (2 * (i : ℝ) + 1) - Real.sign (2 * (i : ℝ) - 2 * n + 1) =
      ((Int.sign (2 * i + 1) - Int.sign (2 * i - 2 * (n : ℤ) + 1) : ℤ) : ℝ) := by
    simp [← Real.sign_intCast]
  rw [hs, intSign_sub_eq_two_mul_indicator]
  split_ifs <;> norm_num

end Matrix
