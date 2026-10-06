import SympyProofs.RouthHurwitz.Table.Basic
import Mathlib.Basic.Real.Basic

/-! Polynomial interpretation of table rows, shared by regular and repaired steps. -/

namespace RouthHurwitz
open Polynomial

/-- Repairs preserve the degree padding, including both exceptional cases. -/
theorem repairRow_support {K : Type*} [Field K] [DecidableEq K]
    (d w : ℕ) (previous raw : Row K)
    (hs : ∀ j, d - 1 < 2 * j → raw j = 0)
    (j : ℕ) (hj : d - 1 < 2 * j) : repairRow d w previous raw j = 0 := by
  by_cases hn : (nonzeroIndices w raw).Nonempty
  · by_cases hz : raw 0 = 0
    · simp only [repairRow, ite_eq_left hn, ite_eq_left hz, shiftRow]
      split
      · simp [hs j hj, hs (j + firstNonzero w raw) (by omega)]
      · exact hs j hj
    · simpa [repairRow, hn, hz] using hs j hj
  · simp [repairRow, hn, derivativeRow, show d - 2 * j = 0 by omega]

section RowEncoding

variable {K : Type*} [Field K]

/-- Interpret the active coefficients of a row as a polynomial of the
indicated parity. Entries past its degree are discarded. -/
noncomputable def encodeRow : ℕ → Row K → K[X]
  | 0, r => C (r 0)
  | 1, r => C (r 0) * X
  | d + 2, r => C (r 0) * X ^ (d + 2) + encodeRow d (fun j => r (j + 1))

theorem encodeRow_congr (d : ℕ) (r s : Row K)
    (h : ∀ j, 2 * j ≤ d → r j = s j) : encodeRow d r = encodeRow d s := by
  induction d using Nat.twoStepInduction generalizing r s with
  | zero => simp [encodeRow, h 0 (by omega)]
  | one => simp [encodeRow, h 0 (by omega)]
  | more d ih _ =>
      simp only [encodeRow, h 0 (by omega)]
      congr 1
      exact ih _ _ (fun j hj => h (j + 1) (by omega))

theorem encodeRow_sub_smul (d : ℕ) (r s : Row K) (c : K) :
    encodeRow d (fun j => r j - c * s j) = encodeRow d r - C c * encodeRow d s := by
  induction d using Nat.twoStepInduction generalizing r s with
  | zero => simp [encodeRow, map_sub, map_mul]
  | one => simp only [encodeRow, map_sub, map_mul]; ring
  | more d ih _ => simp only [encodeRow, ih, map_sub, map_mul]; ring

theorem X_mul_encodeRow (d : ℕ) (r : Row K)
    (hs : ∀ j, d < 2 * j → r j = 0) : X * encodeRow d r = encodeRow (d + 1) r := by
  induction d using Nat.twoStepInduction generalizing r with
  | zero => simp only [encodeRow]; ring
  | one => simp [encodeRow, hs 1 (by omega), pow_two]; ring
  | more d ih _ =>
      have ht := ih (fun j => r (j + 1)) (fun j hj => hs (j + 1) (by omega))
      simp only [encodeRow]
      rw [← ht]
      simp only [pow_succ]
      ring

theorem nextRow_eq_sub (u v : Row K) (hv : v 0 ≠ 0) :
    nextRow u v = fun j => u (j + 1) - (u 0 / v 0) * v (j + 1) := by
  funext j
  dsimp [nextRow]
  field_simp

/-- The ordinary entrywise elimination equation yields the polynomial
Routh recurrence, with padding justified by the row's degree. -/
theorem encodeRow_recurrence (d : ℕ) (u v : Row K) (hv : v 0 ≠ 0)
    (hs : ∀ j, d + 1 < 2 * j → v j = 0) :
    encodeRow (d + 2) u = C (u 0 / v 0) * X * encodeRow (d + 1) v +
      encodeRow d (nextRow u v) := by
  rw [mul_assoc, X_mul_encodeRow (d + 1) v hs, nextRow_eq_sub u v hv,
    encodeRow_sub_smul]
  simp only [encodeRow]
  have hp : C (u 0 / v 0) * C (v 0) = C (u 0) := by
    rw [← map_mul, div_mul_cancel₀ _ hv]
  linear_combination -(X ^ (d + 2)) * hp

theorem coeff_encodeRow (d : ℕ) (r : Row K) (k : ℕ) :
    (encodeRow d r).coeff k =
      if k ≤ d ∧ (d - k) % 2 = 0 then r ((d - k) / 2) else 0 := by
  induction d using Nat.twoStepInduction generalizing r with
  | zero => simp [encodeRow, coeff_C]
  | one =>
      by_cases hk : k = 1
      · subst k; simp [encodeRow]
      · have hc : ¬ (k ≤ 1 ∧ (1 - k) % 2 = 0) := by omega
        simp only [encodeRow, coeff_C_mul_X, ite_eq_right hk, ite_eq_right hc]
  | more d ih _ =>
      rw [encodeRow, coeff_add, coeff_C_mul_X_pow, ih]
      by_cases hk : k = d + 2
      · subst k
        simp [show ¬ d + 2 ≤ d by omega]
      · by_cases hkd : k ≤ d
        · have hk' : k ≤ d + 2 := by omega
          have hm : (d + 2 - k) % 2 = (d - k) % 2 := by omega
          have hd : (d + 2 - k) / 2 = (d - k) / 2 + 1 := by omega
          simp [hk, hkd, hk', hm, hd]
        · have hc : ¬ (k ≤ d + 2 ∧ (d + 2 - k) % 2 = 0) := by omega
          simp [hk, hkd, hc]

/-- Row encoding has the advertised degree bound, even before repair. -/
theorem encodeRow_natDegree_le (d : ℕ) (r : Row K) : (encodeRow d r).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [coeff_encodeRow, not_le.mpr hk]

/-- A nonzero pivot makes the row's advertised degree exact. -/
theorem encodeRow_natDegree (d : ℕ) (r : Row K) (hr : r 0 ≠ 0) :
    (encodeRow d r).natDegree = d := by
  apply le_antisymm (encodeRow_natDegree_le d r)
  apply le_natDegree_of_ne_zero
  simpa [coeff_encodeRow] using hr

end RowEncoding

/-- Coefficients in descending order for interpreting the initial row pair. -/
def descendingCoefficients {K : Type*} [Semiring K] (p : K[X]) (k : ℕ) : K := p.coeff (p.natDegree - k)

theorem initial_polynomials (p : ℝ[X]) (hn : 0 < p.natDegree) :
    encodeRow p.natDegree (initialRow p.natDegree (descendingCoefficients p) 0) +
      encodeRow (p.natDegree - 1) (initialRow p.natDegree (descendingCoefficients p) 1) = p := by
  ext k
  rw [coeff_add, coeff_encodeRow, coeff_encodeRow]
  by_cases hk : k ≤ p.natDegree
  · by_cases hm : (p.natDegree - k) % 2 = 0
    · have ho : ¬ (k ≤ p.natDegree - 1 ∧ (p.natDegree - 1 - k) % 2 = 0) := by omega
      have hb : 2 * ((p.natDegree - k) / 2) ≤ p.natDegree := by omega
      have he : p.natDegree - 2 * ((p.natDegree - k) / 2) = k := by omega
      simp [hk, hm, ho, initialRow, hb, descendingCoefficients, he]
    · have hk' : k ≤ p.natDegree - 1 := by omega
      have hm' : (p.natDegree - 1 - k) % 2 = 0 := by omega
      have hb : 2 * ((p.natDegree - 1 - k) / 2) + 1 ≤ p.natDegree := by omega
      have he : p.natDegree - (2 * ((p.natDegree - 1 - k) / 2) + 1) = k := by omega
      simp [hk, hm, hk', hm', initialRow, hb, descendingCoefficients, he]
  · have hk' : ¬ k ≤ p.natDegree - 1 := by omega
    simp [hk, hk', coeff_eq_zero_of_natDegree_lt (show p.natDegree < k by omega)]


end RouthHurwitz
