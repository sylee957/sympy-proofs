module

public import SympyProofs.Sum.ModularShifts.Algorithm

/-! Correctness of denominator clearing and primitive integer representatives. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

theorem commonDenominator_ne_zero (p : Polynomial ℚ) : commonDenominator p ≠ 0 := by
  exact Finset.lcm_ne_zero_iff.mpr (fun i _ => Rat.den_ne_zero _)

theorem coeff_den_dvd_commonDenominator (p : Polynomial ℚ) (i : ℕ) :
    (p.coeff i).den ∣ commonDenominator p := by
  by_cases hi : i ∈ p.support
  · exact Finset.dvd_lcm hi
  · have hz : p.coeff i = 0 := by simpa only [mem_support_iff, not_not] using hi
    simp [hz]

@[simp] theorem coeff_clearDenominators (p : Polynomial ℚ) (i : ℕ) :
    (clearDenominators p).coeff i =
      (p.coeff i).num * (commonDenominator p / (p.coeff i).den : ℕ) := by
  classical
  simp +contextual [clearDenominators, Polynomial.sum_def, coeff_monomial]

theorem map_clearDenominators (p : Polynomial ℚ) :
    (clearDenominators p).map (Int.castRingHom ℚ) = C (commonDenominator p : ℚ) * p := by
  ext i
  simp only [coeff_map, coeff_clearDenominators, Int.coe_castRingHom, Int.cast_mul,
    Int.cast_natCast, coeff_C_mul]
  rw [Nat.cast_div_charZero (coeff_den_dvd_commonDenominator p i)]
  calc
    _ = (commonDenominator p : ℚ) *
        ((p.coeff i).num / (p.coeff i).den) := by ring
    _ = _ := by rw [Rat.num_div_den]

/-- The primitive integer representative of a monic input differs only by its
integer leading coefficient. Consequently it has the same roots and shift overlaps. -/
theorem primitive_map (p : Polynomial ℚ) (hp : p.Monic) :
    (clearDenominators p).primPart.map (Int.castRingHom ℚ) =
      C ((clearDenominators p).primPart.leadingCoeff : ℚ) * p := by
  let P := clearDenominators p
  have hP : P ≠ 0 := by
    intro hz
    have he := map_clearDenominators p
    rw [show clearDenominators p = 0 from hz, Polynomial.map_zero] at he
    have hd : (commonDenominator p : ℚ) ≠ 0 := by
      exact_mod_cast commonDenominator_ne_zero p
    exact (mul_ne_zero (C_ne_zero.mpr hd) hp.ne_zero) he.symm
  have hc : (P.content : ℚ) ≠ 0 := by
    exact_mod_cast (content_eq_zero_iff.not.mpr hP)
  have he : C (P.content : ℚ) * P.primPart.map (Int.castRingHom ℚ) =
      C (commonDenominator p : ℚ) * p := by
    change C ((Int.castRingHom ℚ) P.content) * _ = _
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← P.eq_C_content_mul_primPart]
    exact map_clearDenominators p
  have hscale : P.primPart.map (Int.castRingHom ℚ) =
      C ((commonDenominator p : ℚ) / P.content) * p := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hc)
    rw [he, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hc]
  have hlc := congrArg Polynomial.leadingCoeff hscale
  simp only [leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int,
    leadingCoeff_mul, leadingCoeff_C, hp.leadingCoeff, mul_one, Int.coe_castRingHom] at hlc
  change P.primPart.map (Int.castRingHom ℚ) = C (P.primPart.leadingCoeff : ℚ) * p
  rw [hlc]
  exact hscale

/-- Clearing denominators and taking the primitive part preserve the input degree. -/
theorem primitive_natDegree (p : Polynomial ℚ) (hp : p.Monic) :
    (clearDenominators p).primPart.natDegree = p.natDegree := by
  have hlc : ((clearDenominators p).primPart.leadingCoeff : ℚ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr (primPart_ne_zero (clearDenominators p))
  have he := congrArg Polynomial.natDegree (primitive_map p hp)
  simpa only [natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    natDegree_C_mul hlc] using he

end Gosper.ModularShifts
