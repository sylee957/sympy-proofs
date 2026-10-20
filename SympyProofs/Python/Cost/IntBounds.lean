module

public import SympyProofs.Python.Cost.Int
public import SympyProofs.Python.Cost.Bounds
public import SympyProofs.Python.Cost.Width
/-! # Value-preserving cost contracts for integer primitives -/

@[expose] public section

namespace Python.Cost.Int
open PythonInt Models
variable {I : Type} [PythonInt I]
theorem eq_bounded (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w)
    (hb : width (toInt b) ≤ w) :
    Bounded schoolbook (eq a b) (fun r => r = (a == b)) (w+1) := by
  apply (RunsWith.perform _ (a == b)).bounded (post := fun r => r = (a == b)) rfl
  change 1 + max (width (toInt a)) (width (toInt b)) ≤ w+1
  omega

theorem div_bounded (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w)
    (hb : width (toInt b) ≤ w) (hr : width (toInt (a/b)) ≤ w) :
    Bounded schoolbook (floorDiv a b) (fun r => r = a/b) (1+w*w+3*w) := by
  apply (RunsWith.perform _ (a/b)).bounded (post := fun r => r = a/b) rfl
  change 1 + (width (toInt a)*width (toInt b)+width (toInt a)+width (toInt b)+width (toInt (a/b))) ≤ _
  have := Nat.mul_le_mul ha hb
  omega

theorem add_bounded (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w)
    (hb : width (toInt b) ≤ w) :
    Bounded schoolbook (add a b) (fun r => r = a+b) (2*w+2) := by
  apply (RunsWith.perform _ (a+b)).bounded (post := fun r => r = a+b) rfl
  have hr := width_add (toInt a) (toInt b)
  change 1+ (max (width (toInt a)) (width (toInt b)) + width (toInt (a+b))) ≤ _
  rw [toInt_add]
  omega

theorem sub_bounded (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w)
    (hb : width (toInt b) ≤ w) :
    Bounded schoolbook (sub a b) (fun r => r = a-b) (2*w+2) := by
  apply (RunsWith.perform _ (a-b)).bounded (post := fun r => r = a-b) rfl
  have hr := width_sub (toInt a) (toInt b)
  change 1+ (max (width (toInt a)) (width (toInt b)) + width (toInt (a-b))) ≤ _
  rw [toInt_sub]
  omega

/-- Reuse a primitive contract under any pointwise cheaper policy. -/
theorem eq_bounded_of_le (model : Model) (hle : ∀ e, model e ≤ schoolbook e)
    (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w) (hb : width (toInt b) ≤ w) :
    Bounded model (eq a b) (fun r => r = (a == b)) (w+1) :=
  (eq_bounded a b w ha hb).reprice_perform (hle _)

theorem div_bounded_of_le (model : Model) (hle : ∀ e, model e ≤ schoolbook e)
    (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w) (hb : width (toInt b) ≤ w)
    (hr : width (toInt (a/b)) ≤ w) :
    Bounded model (floorDiv a b) (fun r => r = a/b) (1+w*w+3*w) :=
  (div_bounded a b w ha hb hr).reprice_perform (hle _)

theorem add_bounded_of_le (model : Model) (hle : ∀ e, model e ≤ schoolbook e)
    (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w) (hb : width (toInt b) ≤ w) :
    Bounded model (add a b) (fun r => r = a+b) (2*w+2) :=
  (add_bounded a b w ha hb).reprice_perform (hle _)

theorem sub_bounded_of_le (model : Model) (hle : ∀ e, model e ≤ schoolbook e)
    (a b : I) (w : ℕ) (ha : width (toInt a) ≤ w) (hb : width (toInt b) ≤ w) :
    Bounded model (sub a b) (fun r => r = a-b) (2*w+2) :=
  (sub_bounded a b w ha hb).reprice_perform (hle _)

end Python.Cost.Int
