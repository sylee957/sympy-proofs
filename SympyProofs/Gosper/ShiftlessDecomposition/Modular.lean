module

public import SympyProofs.Gosper.ShiftlessDecomposition.Correctness
public import SympyProofs.Gosper.ModularShifts.Correctness

/-! The modular shift algorithm satisfies the decomposition's primitive contract. -/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

/-- Modular shifts supplies the required enumeration on monic square-free inputs. -/
theorem modularPrimitives_valid (ops : ModularShifts.Backend) (hops : ops.Valid) :
    ({ gcd := GCDMonoid.gcd, derivative := Polynomial.derivative,
       shifts := ModularShifts.shifts ops } : Primitives ℚ).Valid where
  gcd_eq _ _ := rfl
  derivative_eq _ := rfl
  mem_shifts := ModularShifts.mem_shifts ops hops
  nodup_shifts p q _ _ _ _ := ModularShifts.nodup_shifts ops p q

/-- End-to-end correctness with modular enumeration. The decomposition establishes
monicity and square-freeness at every shift call. -/
theorem decompose_modular_sound (ops : ModularShifts.Backend) (hops : ops.Valid)
    (D : Polynomial ℚ) (hD : D ≠ 0) :
    Valid D (decompose
      { gcd := GCDMonoid.gcd
        derivative := Polynomial.derivative
        shifts := ModularShifts.shifts ops } D) :=
  decompose_sound _ (modularPrimitives_valid ops hops) D hD

end Gosper.ShiftlessDecomposition
