import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Routh–Hurwitz table construction

This models the arithmetic in `sympy/physics/control/routh_table.py`, including
the derivative replacement for a zero row and the signed shift for a zero
first column. Coefficients are supplied in descending order, with an explicit
degree bound. The imperative runner supplies a polynomial’s actual degree and coefficients.

This file contains only local row operations, widths, and initialization.
`Invariant.lean` proves correctness by initialization, preservation, and
termination of a mathematical loop invariant. The executable loops are in
`Imperative.Basic`, `Exact.Basic`, and `Parametric.Basic`. A Python implementation refinement
is outside this model.
-/

namespace RouthHurwitz

open Finset Polynomial

/-- Rows are zero-padded sequences, with active width supplied separately. -/
abbrev Row (K : Type*) := ℕ → K

section Field

variable {K : Type*} [Field K]

/-- The ordinary Routh elimination step, before exceptional-row repair. -/
def nextRow (upper lower : Row K) (j : ℕ) : K :=
  (lower 0 * upper (j + 1) - upper 0 * lower (j + 1)) / lower 0

/-- Zero padding is preserved by ordinary elimination. -/
theorem nextRow_zero (upper lower : Row K) (j : ℕ)
    (hu : upper (j + 1) = 0) (hl : lower (j + 1) = 0) :
    nextRow upper lower j = 0 := by
  simp [nextRow, hu, hl]

/-- Coefficients used to replace an all-zero row, from the preceding row. -/
def derivativeRow (d : ℕ) (r : Row K) : Row K :=
  fun j => r j * (d - 2 * j : ℕ)

theorem derivativeRow_pivot (d : ℕ) (r : Row K) :
    derivativeRow d r 0 = r 0 * (d : K) := by
  simp [derivativeRow]

theorem derivativeRow_pivot_ne_zero [CharZero K] (d : ℕ) (r : Row K)
    (hd : d ≠ 0) (hr : r 0 ≠ 0) : derivativeRow d r 0 ≠ 0 := by
  rw [derivativeRow_pivot]
  exact mul_ne_zero hr (Nat.cast_ne_zero.mpr hd)

variable [DecidableEq K]

/-- Indices of nonzero entries in the active part of a row. -/
def nonzeroIndices (w : ℕ) (r : Row K) : Finset ℕ :=
  (range w).filter (fun j => r j ≠ 0)

/-- The number of leading zeros; returns zero for an entirely zero row. -/
def firstNonzero (w : ℕ) (r : Row K) : ℕ :=
  if h : (nonzeroIndices w r).Nonempty then (nonzeroIndices w r).min' h else 0

theorem firstNonzero_spec (w : ℕ) (r : Row K)
    (h : (nonzeroIndices w r).Nonempty) :
    firstNonzero w r < w ∧ r (firstNonzero w r) ≠ 0 := by
  unfold firstNonzero
  rw [dif_pos h]
  simpa only [nonzeroIndices, mem_filter, mem_range] using
    (Finset.min'_mem (nonzeroIndices w r) h)

theorem before_firstNonzero (w : ℕ) (r : Row K)
    (h : (nonzeroIndices w r).Nonempty) (j : ℕ)
    (hj : j < firstNonzero w r) : r j = 0 := by
  by_contra hn
  have hw := (firstNonzero_spec w r h).1
  have hm : j ∈ nonzeroIndices w r := by
    simp only [nonzeroIndices, mem_filter, mem_range]
    exact ⟨by omega, hn⟩
  have := Finset.min'_le (nonzeroIndices w r) j hm
  simp only [firstNonzero, dif_pos h] at hj
  omega

/-- SymPy's extended-table update after `k` leading zeros.
Only entries whose shifted source is active are changed. -/
def shiftRow (w k : ℕ) (r : Row K) : Row K :=
  fun j => if j + k < w then r j + (-1 : K) ^ k * r (j + k) else r j

theorem shiftRow_pivot_ne_zero (w : ℕ) (r : Row K)
    (h : (nonzeroIndices w r).Nonempty) (hzero : r 0 = 0) :
    shiftRow w (firstNonzero w r) r 0 ≠ 0 := by
  have hs := firstNonzero_spec w r h
  simpa [shiftRow, hs.1, hzero] using
    (mul_ne_zero (pow_ne_zero (firstNonzero w r) (neg_ne_zero.mpr one_ne_zero)) hs.2)

/-- Repair a row exactly by the two branches in `_handle_special_cases`.
`d` is the degree of the auxiliary polynomial from the preceding row. -/
def repairRow (d w : ℕ) (previous raw : Row K) : Row K :=
  if (nonzeroIndices w raw).Nonempty then
    if raw 0 = 0 then shiftRow w (firstNonzero w raw) raw else raw
  else derivativeRow d previous

theorem repairRow_pivot_ne_zero (d w : ℕ) (previous raw : Row K)
    (h : (nonzeroIndices w raw).Nonempty) :
    repairRow d w previous raw 0 ≠ 0 := by
  by_cases hz : raw 0 = 0
  · simpa [repairRow, h, hz] using shiftRow_pivot_ne_zero w raw h hz
  · simp [repairRow, h, hz]

/-- In characteristic zero, repair always supplies a nonzero pivot if the
preceding pivot is nonzero and the auxiliary degree is positive. -/
theorem repairRow_pivot_ne_zero_of_previous [CharZero K]
    (d w : ℕ) (previous raw : Row K) (hd : d ≠ 0) (hp : previous 0 ≠ 0) :
    repairRow d w previous raw 0 ≠ 0 := by
  by_cases h : (nonzeroIndices w raw).Nonempty
  · exact repairRow_pivot_ne_zero d w previous raw h
  · simpa [repairRow, h] using derivativeRow_pivot_ne_zero d previous hd hp

/-- Alternating descending coefficients, with explicit zero padding.
`a k` is the coefficient of degree `n-k`, not the coefficient of degree `k`. -/
def initialRow (n : ℕ) (a : ℕ → K) (parity : ℕ) : Row K :=
  fun j => if 2 * j + parity ≤ n then a (2 * j + parity) else 0

/-- Number of columns allocated by SymPy. -/
def width (n : ℕ) : ℕ := n / 2 + 1

/-- The active prefix for row `i`, matching `_calculate_row`. -/
def activeWidth (n i : ℕ) : ℕ := width n - i / 2

/-- Restrict an ordinary elimination step to its active prefix. -/
def boundedNextRow (w : ℕ) (upper lower : Row K) : Row K :=
  fun j => if j < w then nextRow upper lower j else 0

end Field

end RouthHurwitz
