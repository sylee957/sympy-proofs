module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Field
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Canonical polynomial numerator and monic denominator over an executable field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Poly

open Polynomial
open scoped Polynomial

variable {F G : Type} [Field F] [DecidableEq F] [Field G]

/-- Cancel the polynomial gcd and scale the denominator to be monic. -/
def reduced (p q : Poly F) : Poly F × Poly F :=
  if q = 0 then (0, 1)
  else
    let g := gcd p q
    let d := q / g
    let u := C d.leadingCoeff⁻¹
    (u * (p / g), u * d)

/-- Interpret a computable polynomial over an isomorphic coefficient field. -/
noncomputable def interpret (e : F ≃+* G) : Poly F ≃+* G[X] := equiv.trans (mapEquiv e)

@[simp] theorem interpret_apply (e : F ≃+* G) (p : Poly F) :
    interpret e p = (equiv p).map e := rfl

open scoped Classical in
theorem interpret_gcd (e : F ≃+* G) (p q : Poly F) :
    interpret e (gcd p q) = GCDMonoid.gcd (interpret e p) (interpret e q) := by
  classical
  let f := interpret e
  have h₁ : f (gcd p q) ∣ GCDMonoid.gcd (f p) (f q) :=
    dvd_gcd (map_dvd f (gcd_dvd_left p q)) (map_dvd f (gcd_dvd_right p q))
  have h₂ : f.symm (GCDMonoid.gcd (f p) (f q)) ∣ gcd p q := dvd_gcd
    (by simpa using map_dvd f.symm (gcd_dvd_left (f p) (f q)))
    (by simpa using map_dvd f.symm (gcd_dvd_right (f p) (f q)))
  have hass := associated_of_dvd_dvd h₁ (by simpa using map_dvd f h₂)
  have hn : normalize (f (gcd p q)) = f (gcd p q) := by
    by_cases h : p = 0 ∧ q = 0
    · obtain ⟨rfl,rfl⟩ := h
      simp
    · apply Polynomial.Monic.normalize_eq_self
      simp [f, Polynomial.Monic, Polynomial.leadingCoeff_map, h]
  exact hn.symm.trans ((normalize_eq_normalize_iff_associated.mpr hass).trans (normalize_gcd _ _))

/-- The reduced pair gives exactly Mathlib's chosen numerator and denominator. -/
theorem interpret_reduced (e : F ≃+* G) (p q : Poly F) :
    let z : RatFunc G := algebraMap G[X] _ (interpret e p) / algebraMap G[X] _ (interpret e q)
    (interpret e (reduced p q).1, interpret e (reduced p q).2) = (z.num, z.denom) := by
  classical
  dsimp only
  by_cases hq : q = 0
  · simp [hq, reduced]
  · have hq' : interpret e q ≠ 0 := (map_ne_zero_iff _ (interpret e).injective).mpr hq
    rw [RatFunc.num_div, RatFunc.denom_div _ hq', reduced, ite_eq_right hq]
    have hdiv (a b : Poly F) : interpret e (a / b) = interpret e a / interpret e b := by
      simp [Polynomial.map_div]
    have hl (a : Poly F) : (interpret e a).leadingCoeff = e a.leadingCoeff := by
      simp [Polynomial.leadingCoeff_map]
    have hc (a : F) : interpret e (C a) = Polynomial.C (e a) := by simp
    simp only [map_mul, hc, map_inv₀, ← hl, hdiv, interpret_gcd]

end SympyProofs.Calculus.Antiderivative.Poly
