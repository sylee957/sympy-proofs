module

public import SympyProofs.Gosper.ModularShifts.Support

/-! Exact candidate verification using gcds of the cached integer polynomials. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

theorem primitive_associated (p : Polynomial ℚ) (hp : p.Monic) :
    Associated ((clearDenominators p).primPart.map (Int.castRingHom ℚ)) p := by
  rw [primitive_map p hp]
  apply associated_unit_mul_left
  apply isUnit_C.mpr
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast primitive_leadingCoeff_ne_zero p

/-- Positive-degree integer gcds detect exactly the common factors over ℚ. -/
theorem integer_gcd_pos_iff (P Q : Polynomial ℤ) (hP : P ≠ 0) :
    0 < (GCDMonoid.gcd P Q).natDegree ↔
      ¬IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) := by
  let φ := Int.castRingHom ℚ
  constructor
  · intro hpos hcop
    have hu := hcop.isUnit_of_dvd'
      ((Polynomial.mapRingHom φ).map_dvd (gcd_dvd_left P Q))
      ((Polynomial.mapRingHom φ).map_dvd (gcd_dvd_right P Q))
    have hz := natDegree_eq_zero_of_isUnit hu
    change ((GCDMonoid.gcd P Q).map φ).natDegree = 0 at hz
    rw [natDegree_map_eq_of_injective φ.injective_int] at hz
    omega
  · intro hov
    let d := GCDMonoid.gcd (P.map φ) (Q.map φ)
    have hPm : P.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective_int).mpr hP
    have hdm : d.Monic := by
      dsimp [d]
      rw [← normalize_gcd]
      exact monic_normalize (fun hz => hPm ((gcd_eq_zero_iff _ _).mp hz).1)
    have hdpos : 0 < d.natDegree := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hd1 := hdm.natDegree_eq_zero.mp hz
      apply hov
      apply (gcd_isUnit_iff _ _).mp
      change IsUnit d
      rw [hd1]
      exact isUnit_one
    let D := (clearDenominators d).primPart
    have hassoc : Associated (D.map φ) d := primitive_associated d hdm
    have hdP : D ∣ P :=
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast D P
        (isPrimitive_primPart _)).mpr (hassoc.dvd_iff_dvd_left.mpr (gcd_dvd_left _ _))
    have hdQ : D ∣ Q :=
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast D Q
        (isPrimitive_primPart _)).mpr (hassoc.dvd_iff_dvd_left.mpr (gcd_dvd_right _ _))
    have hdeg : D.natDegree = d.natDegree := by
      rw [← natDegree_map_eq_of_injective φ.injective_int D]
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
    have hg : GCDMonoid.gcd P Q ≠ 0 := fun hz => hP ((gcd_eq_zero_iff _ _).mp hz).1
    have hDpos : 0 < D.natDegree := by simpa [hdeg] using hdpos
    exact hDpos.trans_le (natDegree_le_of_dvd (dvd_gcd hdP hdQ) hg)

theorem integer_shift_overlap_iff (p q : Polynomial ℚ) (hp : p.Monic) (hq : q.Monic)
    (h : ℤ) :
    0 < (GCDMonoid.gcd (clearDenominators p).primPart
      (taylor h (clearDenominators q).primPart)).natDegree ↔
      ¬IsCoprime p (taylor (h : ℚ) q) := by
  rw [integer_gcd_pos_iff _ _ (primPart_ne_zero _), map_taylor]
  have hp' := primitive_associated p hp
  have hq' := (primitive_associated q hq).map (taylorAlgHom (h : ℚ)).toRingHom
  apply not_congr
  constructor
  · intro hc
    exact IsCoprime.mono hp'.symm.dvd hq'.symm.dvd hc
  · intro hc
    exact IsCoprime.mono hp'.dvd hq'.dvd hc

end Gosper.ModularShifts
