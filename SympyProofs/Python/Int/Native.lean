module

public import SympyProofs.Python.Int
public import SympyProofs.Python.Bitwise.Nat
public import Mathlib.Algebra.Ring.TransferInstance

/-! # Native realization of the Python integer interface -/

@[expose] public section

/-- A distinct carrier so Python floor division does not change Lean's `Int` instances. -/
structure PythonInt.Native where
  value : ℤ
  deriving Repr

namespace PythonInt.Native

/-- Transport the standard integer ring and order to the native wrapper. -/
def equiv : Native ≃ ℤ where
  toFun := Native.value
  invFun := Native.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing Native := equiv.commRing
instance : LinearOrder Native := LinearOrder.lift' Native.value equiv.injective

instance : PythonInt Native where
  toCommRing := inferInstance
  toLinearOrder := inferInstance
  equivInt := equiv.ringEquiv
  div x y := ⟨x.value.fdiv y.value⟩
  mod x y := ⟨x.value.fmod y.value⟩
  pow x y := ⟨x.value ^ y.value.toNat⟩
  and x y := ⟨Int.land x.value y.value⟩
  shiftLeft x y := ⟨x.value <<< y.value.toNat⟩
  shiftRight x y := ⟨x.value >>> y.value.toNat⟩
  bitCount x := ⟨Python.Bitwise.NatModel.bitCount x.value.natAbs⟩
  bitLength x := ⟨x.value.natAbs.size⟩
  map_div _ _ _ := rfl
  map_mod _ _ _ := rfl
  map_pow _ _ _ := rfl
  map_and _ _ := rfl
  map_shiftLeft x y _ := Int.shiftLeft_eq x.value y.value.toNat
  map_shiftRight x y _ := by
    change x.value >>> y.value.toNat = _
    rw [Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]
    norm_cast
  map_bitCount x := by
    exact congrArg (fun n : ℕ => (n : ℤ)) (Python.Bitwise.NatModel.bitCount_eq_digit_sum x.value.natAbs)
  map_bitLength _ := rfl
  le_iff _ _ := Iff.rfl

instance : ToString Native := ⟨fun x => toString x.value⟩

end PythonInt.Native
