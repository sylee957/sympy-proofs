module

public import SympyProofs.Calculus.Antiderivative.Spec.Value
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split

/-! The canonical pair in the last generator remains canonical after extending coefficients. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Including a lower model field element makes it constant in the top variable. -/
theorem Model.stepEquiv_include (a : M k n) :
    stepEquiv k n (includeVars (Nat.le_succ n) a) = RatFunc.C a := by
  classical
  obtain ⟨b,rfl⟩ := (K.equiv (R := k) (n := n)).surjective a
  rw [← K.equiv_lift, K.stepEquiv_lift]

/-- Joining a polynomial corresponds to its coefficientwise interpretation in the one-step model. -/
theorem val_joinPoly (p : Poly (K R n)) :
    Model.stepEquiv k n (val k (K.joinPoly p)) =
      algebraMap (M k n)[X] _ ((Poly.equiv p).map (val k)) := by
  rw [K.joinPoly, ← Poly.eval_equiv, Poly.equiv_map, Polynomial.eval_map]
  generalize Poly.equiv p = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
  | monomial d a =>
    rw [Polynomial.eval₂_monomial, Polynomial.map_monomial,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, val_lift, Model.stepEquiv_include, val_gen, Model.stepEquiv_last,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X]

private theorem canonical_pair {L : Type} [Field L] (p q : L[X]) (hc : IsCoprime p q)
    (hm : q.Monic) :
    let v : RatFunc L := algebraMap L[X] _ p / algebraMap L[X] _ q
    (p, q) = (v.num, v.denom) := by
  classical
  have hu := hc.isUnit_of_dvd' (gcd_dvd_left p q) (gcd_dvd_right p q)
  have hg : gcd p q = 1 := by simpa only [normalize_gcd] using normalize_eq_one.mpr hu
  dsimp only
  rw [RatFunc.num_div, RatFunc.denom_div _ hm.ne_zero, hg]
  simp [hm.leadingCoeff]

/-- Extending coefficients takes the computed pair to RatFunc's numerator and denominator. -/
theorem val_split (x : K R (n + 1)) :
    let z := Model.stepEquiv k n (val k x)
    ((Poly.equiv x.split.1).map (val k), (Poly.equiv x.split.2).map (val k)) =
      (z.num, z.denom) := by
  classical
  let v := Model.stepEquiv R n (K.equiv x)
  let f : M R n →+* M k n := Model.mapCoefficients k
  have h := K.interpret_split x
  obtain ⟨hn, hd⟩ := Prod.mk.inj h
  have hp : (Poly.equiv x.split.1).map (val k) = v.num.map f := by
    rw [← hn, Poly.interpret_apply, Polynomial.map_map]
    rfl
  have hq : (Poly.equiv x.split.2).map (val k) = v.denom.map f := by
    rw [← hd, Poly.interpret_apply, Polynomial.map_map]
    rfl
  have hv : Model.stepEquiv k n (val k x) =
      algebraMap (M k n)[X] _ (v.num.map f) / algebraMap (M k n)[X] _ (v.denom.map f) := by
    conv_lhs => rw [← K.join_split x, K.join, map_div₀, map_div₀, val_joinPoly, val_joinPoly]
    rw [hp, hq]
  have hm := (RatFunc.monic_denom v).map f
  have hc := v.isCoprime_num_denom.map (Polynomial.mapRingHom f)
  dsimp only
  rw [hp, hq, hv]
  exact canonical_pair _ _ (by simpa only [Polynomial.coe_mapRingHom] using hc) hm

end SympyProofs.Calculus.Antiderivative
