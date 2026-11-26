module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Reference
public import SympyProofs.Calculus.Antiderivative.Proof.Tangent
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Clear
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! Extending a coefficient map through the rational changes of generator used by the compiler. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

open Polynomial

variable {F G : Type} [Field F] [Field G]

/-- Extend a coefficient homomorphism by substituting a transcendental rational function. -/
noncomputable def rationalMap (f : F →+* G) (z : RatFunc G) (hz : Transcendental G z) :
    RatFunc F →+* RatFunc G :=
  IsFractionRing.lift (g := (aeval z).toRingHom.comp (mapRingHom f))
    ((transcendental_iff_injective.mp hz).comp (map_injective _ f.injective))

@[simp] theorem rationalMap_C (f : F →+* G) (z : RatFunc G) (hz : Transcendental G z) (c : F) :
    rationalMap f z hz (RatFunc.C c) = RatFunc.C (f c) := by
  rw [← RatFunc.algebraMap_C, rationalMap, IsFractionRing.lift_algebraMap]
  simp [RatFunc.algebraMap_eq_C]

@[simp] theorem rationalMap_X (f : F →+* G) (z : RatFunc G) (hz : Transcendental G z) :
    rationalMap f z hz RatFunc.X = z := by
  rw [← RatFunc.algebraMap_X, rationalMap, IsFractionRing.lift_algebraMap]
  simp

/-- The fractional-linear tangent coordinate and its rational inverse. -/
noncomputable def tangentValue (i : F) : RatFunc F :=
  -RatFunc.C i * (RatFunc.X - 1) / (RatFunc.X + 1)

private theorem X_ne_constant (c : F) : (RatFunc.X : RatFunc F) ≠ RatFunc.C c := by
  intro h
  apply RatFunc.transcendental_X (K := F)
  rw [h, ← RatFunc.algebraMap_eq_C]
  exact isAlgebraic_algebraMap c

theorem tangent_inverse [CharZero F] {i : F} (hi : i ≠ 0) :
    (RatFunc.C i - tangentValue i) / (RatFunc.C i + tangentValue i) = RatFunc.X := by
  let c : RatFunc F := RatFunc.C i
  let z := (RatFunc.X : RatFunc F)
  have hc : c ≠ 0 := (map_ne_zero_iff _ RatFunc.C_injective).mpr hi
  have hz : z + 1 ≠ 0 := fun h =>
    X_ne_constant (-1 : F) (by simpa [z] using eq_neg_of_add_eq_zero_left h)
  have hh : c + -c * (z-1) / (z+1) = 2*c/(z+1) := by field_simp; ring
  change (c - -c * (z-1) / (z+1)) / (c + -c * (z-1) / (z+1)) = z
  rw [hh]
  field_simp
  ring

theorem tangent_transcendental [CharZero F] {i : F} (hi : i ≠ 0) :
    Transcendental F (tangentValue i) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c,hc⟩
  have h := tangent_inverse hi
  rw [hc, ← map_sub, ← map_add, ← map_div₀] at h
  exact X_ne_constant _ h.symm

/-- Surjectivity follows from the images of the coefficients and the newest generator. -/
theorem rationalMap_surjective (f : F →+* G) (z : RatFunc G) (hz : Transcendental G z)
    (hf : Function.Surjective f) (hx : RatFunc.X ∈ (rationalMap f z hz).fieldRange) :
    Function.Surjective (rationalMap f z hz) := by
  let h := rationalMap f z hz
  have hc (c : G) : RatFunc.C c ∈ h.fieldRange := by
    obtain ⟨a,rfl⟩ := hf c
    exact ⟨RatFunc.C a, rationalMap_C ..⟩
  have hp (p : G[X]) : algebraMap _ (RatFunc G) p ∈ h.fieldRange := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using h.fieldRange.add_mem hp hq
    | monomial i c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      exact h.fieldRange.mul_mem (hc c) (h.fieldRange.pow_mem hx i)
  intro x
  induction x using RatFunc.induction_on with
  | f p q _ => exact h.fieldRange.div_mem (hp p) (hp q)

theorem rationalMap_tangent_surjective [CharZero G] (f : F →+* G) (hf : Function.Surjective f)
    (i : G) (hi : i ≠ 0) : Function.Surjective (rationalMap f _ (tangent_transcendental hi)) := by
  apply rationalMap_surjective _ _ _ hf
  obtain ⟨c,rfl⟩ := hf i
  refine ⟨(RatFunc.C c - RatFunc.X) / (RatFunc.C c + RatFunc.X), ?_⟩
  simp [tangent_inverse hi]

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

/-- The newest-coordinate presentation of a computable field. -/
noncomputable abbrev presentation (R : Type) [CommRing R] [IsDomain R] [DecidableEq R]
    [NormalizedGCDMonoid R] [Div R] (n : ℕ) : K R (n+1) ≃+* RatFunc (M R n) :=
  K.equiv.trans (Model.stepEquiv R n)

@[simp] theorem presentation_lift (a : K R n) :
    presentation R n (K.lift a) = RatFunc.C (K.equiv a) := K.stepEquiv_lift _

@[simp] theorem presentation_gen : presentation R n K.gen = RatFunc.X := K.stepEquiv_gen

/-- Extend a map on the previous computable field by the specified newest generator. -/
noncomputable def substituteHom (f : K R n →+* K S n) (z : K S (n+1))
    (hz : Transcendental (M S n) (presentation S n z)) : K R (n+1) →+* K S (n+1) :=
  (presentation S n).symm.toRingHom.comp
    ((rationalMap (K.equiv.toRingHom.comp (f.comp K.equiv.symm.toRingHom)) _ hz).comp
      (presentation R n).toRingHom)

@[simp] theorem substituteHom_lift (f : K R n →+* K S n) (z : K S (n+1)) (hz) (a : K R n) :
    substituteHom f z hz (K.lift a) = K.lift (f a) := by
  apply (presentation S n).injective
  change presentation S n ((presentation S n).symm
    (rationalMap _ _ hz (presentation R n (K.lift a)))) = _
  rw [RingEquiv.apply_symm_apply, presentation_lift, rationalMap_C, presentation_lift]
  simp

@[simp] theorem substituteHom_gen (f : K R n →+* K S n) (z : K S (n+1)) (hz) :
    substituteHom f z hz K.gen = z := by
  apply (presentation S n).injective
  simp [substituteHom]

/-- Rational functions are generated by the lifted lower field and the newest generator. -/
theorem step_induction (x : K R (n+1)) (P : K R (n+1) → Prop) (hl : ∀ a, P (K.lift a))
    (hx : P K.gen) (ha : ∀ a b, P a → P b → P (a+b)) (hm : ∀ a b, P a → P b → P (a*b))
    (hd : ∀ a b, P a → P b → P (a/b)) : P x := by
  let H := Polynomial.eval₂RingHom (K.lift (R := R) (n := n)) K.gen
  have poly (p : (K R n)[X]) : P (H p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact ha _ _ hp hq
    | monomial i c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply hm
      · simpa [H] using hl c
      · have hx' : P (H X) := by simpa [H] using hx
        induction i with
        | zero => simpa using hl 1
        | succ i ih => rw [pow_succ]; exact hm _ _ ih hx'
  have hp (p : Poly (K R n)) : P (K.joinPoly p) := by
    rw [← K.joinPolyHom_apply]
    exact poly (Poly.equiv p)
  rw [← K.join_split x, K.join]
  exact hd _ _ (hp _) (hp _)

/-- The universal ring homomorphism agrees with the executable canonical numerator/denominator
substitution on every input. -/
theorem substituteHom_apply (f : K R n →+* K S n) (z : K S (n+1)) (hz) (x : K R (n+1)) :
    substituteHom f z hz x = substitute f z x := by
  let H := substituteHom f z hz
  let g := (K.lift : K S n →+* K S (n+1)).comp f
  have hp (p : Poly (K R n)) :
      H (K.joinPoly p) = (p.map g).eval z := by
    rw [← K.joinPolyHom_apply, ← Poly.eval_equiv, Poly.equiv_map, Polynomial.eval_map]
    change H ((Poly.equiv p).eval₂ K.lift K.gen) = _
    rw [Polynomial.hom_eval₂]
    have hcomp : H.comp K.lift = g := RingHom.ext (substituteHom_lift f z hz)
    rw [hcomp, show H K.gen = z from substituteHom_gen ..]
  change H x = (x.split.1.map g).eval z / (x.split.2.map g).eval z
  conv_lhs => rw [← K.join_split x, K.join, map_div₀, hp, hp]

end SympyProofs.Calculus.Antiderivative.Trigonometric
