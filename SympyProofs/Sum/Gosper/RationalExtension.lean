module

public import SympyProofs.Sum.Gosper.Rational

/-! # Passing from domain coefficients to their fraction field -/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

def fractionRingRatFuncHom : RatFunc R →+* RatFunc (FractionRing R) :=
  RatFunc.liftRingHom
    ((algebraMap (FractionRing R)[X] (RatFunc (FractionRing R))).comp
      (Polynomial.mapRingHom (algebraMap R (FractionRing R))))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((RatFunc.algebraMap_injective _).comp
        (Polynomial.map_injective _ (IsFractionRing.injective R (FractionRing R)))))

theorem fractionRingRatFuncHom_polynomial (p : R[X]) :
    fractionRingRatFuncHom (algebraMap R[X] (RatFunc R) p) =
      algebraMap (FractionRing R)[X] (RatFunc (FractionRing R))
        (p.map (algebraMap R (FractionRing R))) :=
  RatFunc.liftRingHom_algebraMap _ _ _

theorem fractionRingRatFuncHom_surjective :
    Function.Surjective (fractionRingRatFuncHom : RatFunc R → RatFunc (FractionRing R)) := by
  have hpoly (p : (FractionRing R)[X]) :
      ∃ f : RatFunc R, fractionRingRatFuncHom f =
        algebraMap (FractionRing R)[X] (RatFunc (FractionRing R)) p := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨f, hf⟩ := hp
      obtain ⟨g, hg⟩ := hq
      exact ⟨f + g, by rw [map_add, hf, hg, map_add]⟩
    | monomial n a =>
      obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective R a
      refine ⟨algebraMap R[X] (RatFunc R) (monomial n u) /
        algebraMap R[X] (RatFunc R) (C v), ?_⟩
      rw [map_div₀, fractionRingRatFuncHom_polynomial, fractionRingRatFuncHom_polynomial]
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        ← C_mul_X_pow_eq_monomial,
        map_mul, map_pow, RatFunc.algebraMap_C, map_div₀]
      ring
  intro f
  induction f using RatFunc.induction_on with
  | f p q hq =>
    obtain ⟨u, hu⟩ := hpoly p
    obtain ⟨v, hv⟩ := hpoly q
    exact ⟨u / v, by rw [map_div₀, hu, hv]⟩

/-- Adjoining coefficient fractions does not change the rational-function field. -/
def fractionRingRatFuncEquiv (R : Type*) [CommRing R] [IsDomain R] :
    RatFunc R ≃+* RatFunc (FractionRing R) :=
  RingEquiv.ofBijective fractionRingRatFuncHom
    ⟨fractionRingRatFuncHom.injective, fractionRingRatFuncHom_surjective⟩

@[simp] theorem fractionRingRatFuncEquiv_polynomial (p : R[X]) :
    fractionRingRatFuncEquiv R (algebraMap R[X] (RatFunc R) p) =
      algebraMap (FractionRing R)[X] (RatFunc (FractionRing R))
        (p.map (algebraMap R (FractionRing R))) :=
  fractionRingRatFuncHom_polynomial p

/-- The coefficient-field equivalence commutes with translation. -/
@[simp] theorem fractionRingRatFuncEquiv_shift (a : R) (f : RatFunc R) :
    fractionRingRatFuncEquiv R (rationalShift a f) =
      rationalShift (algebraMap R (FractionRing R) a) (fractionRingRatFuncEquiv R f) := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    simp only [map_div₀, rationalShift_polynomial, fractionRingRatFuncEquiv_polynomial,
      Polynomial.map_taylor]

end Gosper
