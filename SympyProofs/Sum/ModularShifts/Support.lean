module

public import SympyProofs.Sum.ModularShifts.Contracts
public import SympyProofs.Sum.ModularShifts.Clearing

/-! The primitive integer representatives preserve separability. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

theorem primitive_leadingCoeff_ne_zero (p : Polynomial ℚ) :
    (clearDenominators p).primPart.leadingCoeff ≠ 0 :=
  leadingCoeff_ne_zero.mpr (primPart_ne_zero _)

theorem primitive_separable (p : Polynomial ℚ) (hp : p.Monic) (hs : Squarefree p) :
    ((clearDenominators p).primPart.map (Int.castRingHom ℚ)).Separable := by
  rw [primitive_map p hp]
  have hlc : ((clearDenominators p).primPart.leadingCoeff : ℚ) ≠ 0 := by
    exact_mod_cast primitive_leadingCoeff_ne_zero p
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc))
    (PerfectField.separable_iff_squarefree.mpr hs)

/-- The derivative resultant of a rationally separable integer polynomial is nonzero. -/
theorem resultant_ne_zero_of_rational_separable (P : Polynomial ℤ)
    (hp : (P.map (Int.castRingHom ℚ)).Separable) : P.resultant P.derivative ≠ 0 := by
  have hn := resultant_ne_zero (P.map (Int.castRingHom ℚ))
    (P.derivative.map (Int.castRingHom ℚ))
    (by simpa only [separable_def, ← derivative_map] using hp)
  rw [natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    resultant_map_map] at hn
  intro hz
  exact hn (by rw [hz]; exact map_zero _)

/-- The excluded integer is nonzero on the inputs used by the algorithm. -/
theorem excludedDivisors_pos (ops : Backend) (hs : ResultantValid ops) (P : Polynomial ℤ)
    (hp : (P.map (Int.castRingHom ℚ)).Separable) (hd : P.natDegree ≠ 0) :
    0 < excludedDivisors ops P := by
  have hP : P ≠ 0 := by
    intro hz
    exact hp.ne_zero (by rw [hz, Polynomial.map_zero])
  unfold excludedDivisors
  apply Nat.mul_pos (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hP))
  rw [hs P P.derivative (Or.inl hd)]
  exact Int.natAbs_pos.mpr (resultant_ne_zero_of_rational_separable P hp)

end Gosper.ModularShifts
