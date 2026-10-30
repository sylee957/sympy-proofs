module

public import SympyProofs.Gosper.ModularShifts.Support

/-! Monic reduction of primitive integer inputs at a good prime. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

/-- Avoiding the leading coefficient and derivative resultant gives a nonzero,
separable reduction. The resultant's Bézout identity is used only in the proof. -/
theorem goodIntegerReduction_of_resultant (ops : Backend) (hs : ResultantValid ops)
    (P : Polynomial ℤ) {r : ℕ} (hr : r.Prime) (hbad : ¬r ∣ excludedDivisors ops P) :
    GoodIntegerReduction r P := by
  let : Fact r.Prime := ⟨hr⟩
  have hlc : ¬r ∣ P.leadingCoeff.natAbs := fun h => hbad (dvd_mul_of_dvd_left h _)
  have hl : (P.leadingCoeff : ZMod r) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd P.leadingCoeff r).mp hz
    exact hlc (by simpa using Int.natAbs_dvd_natAbs.mpr hd)
  refine ⟨hl, ?_⟩
  by_cases hd : P.natDegree = 0
  · have he : P = C P.leadingCoeff := by
      simpa [leadingCoeff, hd] using eq_C_of_natDegree_eq_zero hd
    rw [he, Polynomial.map_C]
    exact (separable_C _).mpr (isUnit_iff_ne_zero.mpr hl)
  · have hres : ¬r ∣ (P.resultant P.derivative).natAbs := by
      intro h
      apply hbad
      simpa only [excludedDivisors, hs P P.derivative (Or.inl hd)] using
        (dvd_mul_of_dvd_right h P.leadingCoeff.natAbs)
    have hn : ((P.resultant P.derivative : ℤ) : ZMod r) ≠ 0 := by
      intro hz
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (P.resultant P.derivative) r).mp hz
      exact hres (by simpa using Int.natAbs_dvd_natAbs.mpr h)
    obtain ⟨u, v, _, _, he⟩ :=
      exists_mul_add_mul_eq_C_resultant P P.derivative le_rfl le_rfl (Or.inl hd)
    let φ := Int.castRingHom (ZMod r)
    have hm := congrArg (Polynomial.map φ) he
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← derivative_map] at hm
    refine ⟨C ((P.resultant P.derivative : ℤ) : ZMod r)⁻¹ * u.map φ,
      C ((P.resultant P.derivative : ℤ) : ZMod r)⁻¹ * v.map φ, ?_⟩
    calc
      _ = C ((P.resultant P.derivative : ℤ) : ZMod r)⁻¹ *
          (P.map φ * u.map φ + (P.map φ).derivative * v.map φ) := by ring
      _ = 1 := by
        rw [hm]
        change C ((P.resultant P.derivative : ℤ) : ZMod r)⁻¹ *
          C ((P.resultant P.derivative : ℤ) : ZMod r) = 1
        rw [← C_mul, inv_mul_cancel₀ hn, C_1]

/-- The accepted reduction is a valid input to finite-field factorization. -/
theorem reduce_monic_separable {r : ℕ} (hr : r.Prime) (P : Polynomial ℤ)
    (hp : GoodIntegerReduction r P) : (reduce r P).Monic ∧ (reduce r P).Separable := by
  let : Fact r.Prime := ⟨hr⟩
  have hl : (P.map (Int.castRingHom (ZMod r))).leadingCoeff = (P.leadingCoeff : ZMod r) :=
    leadingCoeff_map_of_leadingCoeff_ne_zero _ hp.1
  refine ⟨?_, ?_⟩
  · rw [reduce, Monic, leadingCoeff_mul, leadingCoeff_C, hl, inv_mul_cancel₀ hp.1]
  · exact Separable.unit_mul
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hp.1))) hp.2

end Gosper.ModularShifts
