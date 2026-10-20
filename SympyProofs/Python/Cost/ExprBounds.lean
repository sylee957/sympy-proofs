module

public import SympyProofs.Python.Cost.Expr
public import SympyProofs.Python.Cost.Bounds
public import SympyProofs.Python.Cost.Width

/-!
# Composing bit costs through ordinary arithmetic

An expression bound carries a result-width bound as well as a work budget.
The rules follow the expression tree; intermediate values need not be expanded.
All costs use the explicit `Models.schoolbook` policy.
-/

@[expose] public section

namespace Python.Cost.CostExpr

open PythonInt Models

variable {I : Type} [PythonInt I]

def Sized (x : CostExpr (CostT Id) I) (bits budget : ℕ) : Prop :=
  Bounded schoolbook x.run (fun a => width (toInt a) ≤ bits) budget

namespace Sized

theorem value (a : I) {bits : ℕ} (h : width (toInt a) ≤ bits) :
    Sized (CostExpr.value a) bits 0 := Bounded.pure a h

theorem mono {x : CostExpr (CostT Id) I} {w c w' c' : ℕ}
    (h : Sized x w c) (hw : w ≤ w') (hc : c ≤ c') : Sized x w' c' :=
  Bounded.mono h (fun _ ha => ha.trans hw) hc

theorem unary {x : CostExpr (CostT Id) I} {w c r d : ℕ}
    (h : Sized x w c) (op : IntOp) (f : I → I)
    (hr : ∀ a, width (toInt a) ≤ w → width (toInt (f a)) ≤ r)
    (hd : ∀ a, width (toInt a) ≤ w →
      schoolbook (.integer ⟨op, [toInt a], toInt (f a)⟩) ≤ d) :
    Sized (CostExpr.unary (Int.unary op f) x) r (c + d) :=
  h.bind fun a ha => (RunsWith.perform _ (f a)).bounded (hr a ha) (hd a ha)

theorem binary {x y : CostExpr (CostT Id) I} {wx wy cx cy r d : ℕ}
    (hx : Sized x wx cx) (hy : Sized y wy cy) (op : IntOp) (f : I → I → I)
    (hr : ∀ a b, width (toInt a) ≤ wx → width (toInt b) ≤ wy →
      width (toInt (f a b)) ≤ r)
    (hd : ∀ a b, width (toInt a) ≤ wx → width (toInt b) ≤ wy →
      schoolbook (.integer ⟨op, [toInt a, toInt b], toInt (f a b)⟩) ≤ d) :
    Sized (CostExpr.binary (Int.binary op f) x y) r (cx + cy + d) := by
  have h := hx.bind fun a ha => hy.bind fun b hb =>
    (RunsWith.perform _ (f a b)).bounded
      (post := fun z => width (toInt z) ≤ r) (hr a b ha hb) (hd a b ha hb)
  simpa only [Sized, CostExpr.binary, Int.binary, Nat.add_assoc] using h

theorem bitCount {x : CostExpr (CostT Id) I} {w c : ℕ} (h : Sized x w c) :
    Sized x.bitCount w (c + (1 + 2 * w)) := by
  apply h.unary .bitCount PythonInt.bitCount
  · intro a ha
    exact (width_bitCount a).trans ha
  · intro a ha
    have hb := width_bitCount a
    simp only [schoolbook, integerSchoolbook, List.getElem?_cons_zero, Option.getD_some]
    omega

theorem add {x y : CostExpr (CostT Id) I} {wx wy cx cy : ℕ}
    (hx : Sized x wx cx) (hy : Sized y wy cy) :
    Sized (x + y) (max wx wy + 1) (cx + cy + (2 * max wx wy + 2)) := by
  apply hx.binary hy .add (· + ·)
  · intro a b ha hb
    rw [toInt_add]
    exact (width_add _ _).trans (Nat.add_le_add_right (max_le_max ha hb) 1)
  · intro a b ha hb
    have hr := width_add (toInt a) (toInt b)
    have hm := max_le_max ha hb
    simp [schoolbook, integerSchoolbook, toInt_add]
    omega

theorem sub {x y : CostExpr (CostT Id) I} {wx wy cx cy : ℕ}
    (hx : Sized x wx cx) (hy : Sized y wy cy) :
    Sized (x - y) (max wx wy + 1) (cx + cy + (2 * max wx wy + 2)) := by
  apply hx.binary hy .sub (· - ·)
  · intro a b ha hb
    rw [toInt_sub]
    exact (width_sub _ _).trans (Nat.add_le_add_right (max_le_max ha hb) 1)
  · intro a b ha hb
    have hr := width_sub (toInt a) (toInt b)
    have hm := max_le_max ha hb
    simp [schoolbook, integerSchoolbook, toInt_sub]
    omega

theorem mul {x y : CostExpr (CostT Id) I} {wx wy cx cy : ℕ}
    (hx : Sized x wx cx) (hy : Sized y wy cy) :
    Sized (x * y) (wx + wy) (cx + cy + (1 + wx * wy + wx + wy)) := by
  apply hx.binary hy .mul (· * ·)
  · intro a b ha hb
    rw [toInt_mul]
    exact (width_mul _ _).trans (Nat.add_le_add ha hb)
  · intro a b ha hb
    have hr := width_mul (toInt a) (toInt b)
    have hm := Nat.mul_le_mul ha hb
    simp [schoolbook, integerSchoolbook, toInt_mul]
    omega

theorem cost_le {x : CostExpr (CostT Id) I} {bits budget : ℕ}
    (h : Sized x bits budget) : (CostT.run x.run schoolbook).2 ≤ budget :=
  Bounded.cost_le h

end Sized

end Python.Cost.CostExpr
