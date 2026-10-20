module

public import SympyProofs.Python.Cost.Models
public import SympyProofs.Python.Int
public import Mathlib.Tactic

/-! # Size bounds for composing integer-operation costs -/

@[expose] public section

namespace Python.Cost.Models

theorem one_le_width (x : ℤ) : 1 ≤ width x := le_max_left _ _

/-- The width convention is one plus the floor base-two logarithm, including zero. -/
theorem width_eq_log2_succ (x : ℤ) : width x = x.natAbs.log2 + 1 := by
  by_cases h : x.natAbs = 0
  · simp [width, h]
  have hu := Nat.size_le.mpr (Nat.lt_log2_self (n := x.natAbs))
  have hl := Nat.lt_size.mpr (Nat.log2_self_le h)
  simp only [width]
  omega

theorem width_mono {x y : ℤ} (h : x.natAbs ≤ y.natAbs) : width x ≤ width y :=
  max_le_max (le_refl _) (Nat.size_le_size h)

@[simp] theorem width_neg (x : ℤ) : width (-x) = width x := by simp [width]

private theorem size_add_le (a b : ℕ) :
    (a + b).size ≤ max a.size b.size + 1 := by
  have ha : a < 2 ^ max a.size b.size := Nat.size_le.mp (le_max_left _ _)
  have hb : b < 2 ^ max a.size b.size := Nat.size_le.mp (le_max_right _ _)
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

theorem width_add (x y : ℤ) : width (x + y) ≤ max (width x) (width y) + 1 := by
  have h := (Nat.size_le_size (Int.natAbs_add_le x y)).trans (size_add_le _ _)
  simp only [width]
  omega

theorem width_sub (x y : ℤ) : width (x - y) ≤ max (width x) (width y) + 1 := by
  simpa [sub_eq_add_neg] using width_add x (-y)

theorem width_mul (x y : ℤ) : width (x * y) ≤ width x + width y := by
  have hx : x.natAbs < 2 ^ width x := Nat.size_le.mp (le_max_right _ _)
  have hy : y.natAbs < 2 ^ width y := Nat.size_le.mp (le_max_right _ _)
  have hsize : (x * y).natAbs.size ≤ width x + width y := by
    apply Nat.size_le.mpr
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hx hy
  have hx1 := one_le_width x
  simp only [width] at *
  omega

theorem width_bitCount {I : Type} [PythonInt I] (x : I) :
    width (PythonInt.toInt (PythonInt.bitCount x)) ≤ width (PythonInt.toInt x) := by
  apply width_mono
  simp only [PythonInt.toInt_bitCount, Int.natAbs_natCast]
  exact Nat.digit_sum_le 2 _

end Python.Cost.Models
