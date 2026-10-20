module

public import SympyProofs.Python.Cost.Index
public import SympyProofs.Python.Cost.Bounds
public import SympyProofs.Python.Cost.Width

/-! # Value and cost contracts for natural storage-index arithmetic -/

@[expose] public section

namespace Python.Cost.Index

open Models

theorem sub_bounded (a b w : ℕ) (ha : width (a : ℤ) ≤ w) (hb : width (b : ℤ) ≤ w) :
    Bounded schoolbook (sub a b) (fun r => r = a - b) (2*w+1) := by
  apply (RunsWith.perform _ (a-b)).bounded (post := fun r => r = (a-b)) rfl
  have hr : width ((a-b : ℕ) : ℤ) ≤ w :=
    (width_mono (by simpa only [Int.natAbs_natCast] using Nat.sub_le a b)).trans ha
  simp only [schoolbook, integerSchoolbook, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  omega

theorem le_bounded (a b w : ℕ) (ha : width (a : ℤ) ≤ w) (hb : width (b : ℤ) ≤ w) :
    Bounded schoolbook (le a b) (fun r => r = decide (a ≤ b)) (w+1) := by
  apply (RunsWith.perform _ (decide (a ≤ b))).bounded (post := fun r => r = (decide (a ≤ b))) rfl
  simp only [schoolbook, integerSchoolbook, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  omega

theorem add_bounded (a b w : ℕ) (ha : width (a : ℤ) ≤ w) (hb : width (b : ℤ) ≤ w) :
    Bounded schoolbook (add a b) (fun r => r = a + b) (2*w+2) := by
  apply (RunsWith.perform _ (a+b)).bounded (post := fun r => r = (a+b)) rfl
  have hr : width ((a+b : ℕ) : ℤ) ≤ w+1 := by
    simpa only [Nat.cast_add] using (width_add (a : ℤ) b).trans
      (Nat.add_le_add_right (max_le ha hb) 1)
  simp only [schoolbook, integerSchoolbook, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  omega

theorem div_bounded (a b wa wb : ℕ) (ha : width (a : ℤ) ≤ wa)
    (hb : width (b : ℤ) ≤ wb) :
    Bounded schoolbook (div a b) (fun r => r = a / b) (1+wa*wb+2*wa+wb) := by
  apply (RunsWith.perform _ (a/b)).bounded (post := fun r => r = (a/b)) rfl
  have hr : width ((a/b : ℕ) : ℤ) ≤ wa :=
    (width_mono (by simpa only [Int.natAbs_natCast] using Nat.div_le_self a b)).trans ha
  have hm := Nat.mul_le_mul ha hb
  simp only [schoolbook, integerSchoolbook, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  omega

end Python.Cost.Index
