module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.List.Range

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed integer ranges

`intRange a b s` models the loop behind `list(range(a, b, s))`: test the
exclusive stop, emit the current integer, add the stride, and repeat. It does
not use a precomputed length. For arbitrary integer endpoints and any nonzero
signed stride, `intRange_eq_map_range` proves equality with the closed-form
ordered progression, and `intRange_length` proves its clipped-ceiling length.
-/

@[expose] public section

namespace SympyProofs.PythonSlice

/-- Whether the `k`th progression term is before the exclusive stop, in slice order. -/
def continues (a b s : ℤ) (k : ℕ) : Prop :=
  if 0 < s then a + (k : ℤ) * s < b else b < a + (k : ℤ) * s

instance (a b s : ℤ) (k : ℕ) : Decidable (continues a b s k) := by
  unfold continues
  infer_instance

/-- Natural ceiling includes the zero clamp for empty slices. Zero steps are invalid. -/
def length (a b s : ℤ) : ℕ := ⌈((b : ℚ) - a) / s⌉₊

/-- Valid for arbitrary signed endpoints, empty intervals, and either step direction. -/
theorem lt_length_iff {a b s : ℤ} {k : ℕ} (hs : s ≠ 0) :
    k < length a b s ↔ continues a b s k := by
  rw [length, Nat.lt_ceil]
  by_cases hp : 0 < s
  · rw [lt_div_iff₀ (show (0 : ℚ) < s by exact_mod_cast hp)]
    have h : ((k : ℚ) * s < (b : ℚ) - a) ↔ (k : ℤ) * s < b - a := by
      exact_mod_cast Iff.rfl
    rw [h]
    simp only [continues, hp, ite_true]
    omega
  · have hn : s < 0 := by omega
    rw [lt_div_iff_of_neg (show (s : ℚ) < 0 by exact_mod_cast hn)]
    have h : ((b : ℚ) - a < (k : ℚ) * s) ↔ b - a < (k : ℤ) * s := by
      exact_mod_cast Iff.rfl
    rw [h]
    simp only [continues, hp, ite_false]
    omega

/-- The explicit integer-valued formula, including empty slices. -/
theorem length_eq_max_ceiling (a b s : ℤ) :
    (length a b s : ℤ) = max 0 ⌈((b : ℚ) - a) / s⌉ := by
  rw [length, ← Int.ceil_toNat, Int.toNat_eq_max, max_comm]

/-- A nonzero signed stride cannot repeat an index. -/
theorem affine_injective {a s : ℤ} (hs : s ≠ 0) :
    Function.Injective (fun k : ℕ => a + (k : ℤ) * s) := by
  intro i j h
  have hmul : (i : ℤ) * s = (j : ℤ) * s := add_left_cancel h
  exact_mod_cast (mul_right_cancel₀ hs hmul)

/-- Operational signed range: repeatedly emit the current index and add the stride. -/
def intRange (a b s : ℤ) (hs : s ≠ 0) : List ℤ :=
  if _h : (if 0 < s then a < b else b < a) then
    a :: intRange (a + s) b s hs
  else []
termination_by if 0 < s then (b - a).toNat else (a - b).toNat
decreasing_by split_ifs at * <;> omega

private theorem continues_succ (a b s : ℤ) (k : ℕ) :
    continues a b s (k + 1) ↔ continues (a + s) b s k := by
  have h : a + ((k + 1 : ℕ) : ℤ) * s = a + s + (k : ℤ) * s := by
    push_cast
    ring
  simp only [continues, h]

private theorem length_eq_succ {a b s : ℤ} (hs : s ≠ 0) (h : continues a b s 0) :
    length a b s = length (a + s) b s + 1 := by
  apply eq_of_forall_lt_iff
  intro k
  cases k with
  | zero => exact iff_of_true ((lt_length_iff hs).2 h) (by omega)
  | succ k =>
    rw [Nat.succ_lt_succ_iff, lt_length_iff hs, lt_length_iff hs]
    exact continues_succ a b s k

private theorem length_eq_zero {a b s : ℤ} (hs : s ≠ 0) (h : ¬continues a b s 0) :
    length a b s = 0 := by
  have : ¬0 < length a b s := fun hk => h ((lt_length_iff hs).1 hk)
  omega

/-- The operational range is exactly the affine progression of the mathematically
predicted length, with the same order and multiplicity. -/
theorem intRange_eq_map_range (a b s : ℤ) (hs : s ≠ 0) :
    intRange a b s hs =
      (List.range (length a b s)).map (fun k : ℕ => a + (k : ℤ) * s) := by
  induction a using intRange.induct b s hs with
  | case1 a h ih =>
    have hc : continues a b s 0 := by simpa [continues] using h
    have heq : intRange a b s hs = a :: intRange (a + s) b s hs := by
      rw [intRange]
      by_cases hp : 0 < s <;> simp_all
    rw [heq, ih, length_eq_succ hs hc]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.cast_zero, zero_mul, add_zero]
    congr 2
    funext k
    simp only [Function.comp_apply, Nat.cast_succ]
    ring
  | case2 a h =>
    have hc : ¬continues a b s 0 := by simpa [continues] using h
    have heq : intRange a b s hs = [] := by
      rw [intRange]
      by_cases hp : 0 < s
      · have hab : ¬a < b := by simpa [continues, hp] using hc
        simp [hp, hab]
      · have hba : ¬b < a := by simpa [continues, hp] using hc
        simp [hp, hba]
    rw [heq, length_eq_zero hs hc]
    rfl

/-- The number of loop iterations is the clipped ceiling, for arbitrary signed endpoints. -/
theorem intRange_length (a b s : ℤ) (hs : s ≠ 0) :
    ((intRange a b s hs).length : ℤ) = max 0 ⌈((b : ℚ) - a) / s⌉ := by
  rw [intRange_eq_map_range, List.length_map, List.length_range, length_eq_max_ceiling]

/-- Exactly the affine progression terms belong to the operational range. -/
theorem mem_intRange {a b s x : ℤ} (hs : s ≠ 0) :
    x ∈ intRange a b s hs ↔
      ∃ k : ℕ, k < length a b s ∧ x = a + (k : ℤ) * s := by
  rw [intRange_eq_map_range]
  simp only [List.mem_map, List.mem_range]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

end SympyProofs.PythonSlice
