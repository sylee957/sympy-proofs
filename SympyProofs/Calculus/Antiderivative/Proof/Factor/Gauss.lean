module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Lifting a factor from the fraction field to the ring of parameter polynomials. -/

public section

namespace SympyProofs.Calculus.Antiderivative.Factor

open scoped nonZeroDivisors Polynomial

/-- A nonzero factor over a fraction field lifts, up to a nonzero scalar, to a divisor over
the coefficient ring. In particular this applies when the coefficient ring is a multivariate
polynomial ring over the constants. -/
theorem lift_fraction_divisor {A L : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
    [Field L] [Algebra A L] [IsFractionRing A L] (p : A[X]) (q : L[X]) (hq : q ≠ 0)
    (hd : q ∣ p.map (algebraMap A L)) :
    ∃ b : A[X], b ∣ p ∧ Associated (b.map (algebraMap A L)) q ∧ b.natDegree = q.natDegree := by
  let z := IsLocalization.integerNormalization A⁰ q
  obtain ⟨d, hd0, he⟩ := IsLocalization.integerNormalization_spec A⁰ q
  change z.map (algebraMap A L) = d • q at he
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at he
  have hm : Function.Injective (algebraMap A L) := IsFractionRing.injective _ _
  have d0 := (map_ne_zero_iff _ hm).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hd0)
  have hz : z ≠ 0 := fun h => hq (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hc0 : z.content ≠ 0 := fun h => hz (Polynomial.content_eq_zero_iff.mp h)
  have hc : IsUnit (Polynomial.C (algebraMap A L z.content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hm).mpr hc0))
  have zz : Associated (z.primPart.map (algebraMap A L)) (z.map (algebraMap A L)) := by
    conv_rhs => rw [z.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C, mul_comm]
    exact associated_mul_unit_right _ _ hc
  have zq : Associated (z.map (algebraMap A L)) q := by
    rw [he, mul_comm]
    exact associated_mul_unit_left _ _ (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr d0))
  refine ⟨z.primPart, ?_, zz.trans zq, ?_⟩
  · apply (z.isPrimitive_primPart.dvd_iff_fraction_map_dvd_fraction_map L).mpr
    exact ((zz.trans zq).dvd_iff_dvd_left.mpr hd)
  · rw [Polynomial.natDegree_primPart, ← Polynomial.natDegree_map_eq_of_injective hm z,
      he, Polynomial.natDegree_C_mul d0]

end SympyProofs.Calculus.Antiderivative.Factor
