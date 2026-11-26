module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Tower
import Mathlib.Tactic.Ring

/-! Clearing coefficient denominators preserves every individual coefficient. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Substitution of the newest generator is a ring homomorphism on univariate polynomials. -/
noncomputable def K.joinPolyHom : Poly (K R n) →+* K R (n + 1) :=
  (Polynomial.eval₂RingHom K.lift K.gen).comp Poly.equiv.toRingHom

@[simp] theorem K.joinPolyHom_apply (p : Poly (K R n)) : K.joinPolyHom p = K.joinPoly p := by
  rw [K.joinPoly, ← Poly.eval_equiv, Poly.equiv_map, Polynomial.eval_map]
  rfl

/-- The polynomial denominator returned by a canonical split represents a nonzero field element. -/
theorem K.joinPoly_split_den_ne (x : K R (n + 1)) : K.joinPoly x.split.2 ≠ 0 := by
  have hd := (Prod.mk.inj (K.interpret_split x)).2
  intro h
  have hh := K.stepEquiv_joinPoly x.split.2
  rw [h, map_zero, map_zero, hd] at hh
  exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _) hh.symm

/-- All numerators returned by `commonDen` represent the corresponding inputs multiplied
by the same nonzero polynomial denominator. -/
theorem commonDen_numerators (xs : List (K R (n + 1))) :
    K.joinPoly (commonDen xs).2 ≠ 0 ∧ List.Forall₂
      (fun x a => K.joinPoly a = x * K.joinPoly (commonDen xs).2) xs (commonDen xs).1 := by
  induction xs with
  | nil =>
    refine ⟨?_, .nil⟩
    change K.joinPoly (1 : Poly (K R n)) ≠ 0
    rw [← K.joinPolyHom_apply, map_one]
    exact one_ne_zero
  | cons x xs ih =>
    have hb := K.joinPoly_split_den_ne x
    have ha := (div_eq_iff hb).mp (K.join_split x)
    have hmul (a b : Poly (K R n)) : K.joinPoly (a * b) = K.joinPoly a * K.joinPoly b :=
      by simpa only [K.joinPolyHom_apply] using (map_mul K.joinPolyHom a b)
    change K.joinPoly (x.split.2 * (commonDen xs).2) ≠ 0 ∧ _
    rw [hmul]
    refine ⟨mul_ne_zero hb ih.1, .cons ?_ ?_⟩
    · change K.joinPoly (x.split.1 * (commonDen xs).2) = _ * K.joinPoly (_ * _)
      rw [hmul, hmul, ha, mul_assoc]
      rfl
    · apply List.forall₂_map_right_iff.mpr
      refine ih.2.imp fun y a he => ?_
      change K.joinPoly (a * x.split.2) = y * K.joinPoly (x.split.2 * (commonDen xs).2)
      rw [hmul, hmul, he, mul_assoc, mul_comm (K.joinPoly (commonDen xs).2)]

namespace Factor

variable {F : Type} [Field F] [DecidableEq F]

/-- Interpret sparse terms with coefficients embedded by a field homomorphism. -/
def termsValue {k : ℕ} (f : K R k →+* F) (vs : List (Poly F))
    (ts : List (List ℕ × K R k)) : Poly F :=
  (ts.map fun (m, c) => Poly.C (f c) * monomialValue vs m).sum

private theorem termsValue_append {k : ℕ} (f : K R k →+* F) (vs : List (Poly F))
    (ts us : List (List ℕ × K R k)) :
    termsValue f vs (ts ++ us) = termsValue f vs ts + termsValue f vs us := by
  simp [termsValue]

private theorem expandedValue (f : K R (n + 1) →+* F) (vs : List (Poly F)) (m : List ℕ)
    (cs : List (K R n)) (start : ℕ) :
    termsValue (f.comp K.lift) (Poly.C (f K.gen) :: vs)
      ((cs.zipIdx start).filterMap fun (a, i) => if a = 0 then none else some (i :: m, a)) =
      Poly.C (f (Poly.Raw.eval K.gen (cs.map K.lift))) *
        (Poly.C (f K.gen)) ^ start * monomialValue vs m := by
  induction cs generalizing start with
  | nil => simp [termsValue, Poly.Raw.eval]
  | cons a cs ih =>
    by_cases ha : a = 0
    · simp only [List.zipIdx_cons, List.filterMap_cons, ha, ↓reduceIte, List.map_cons,
        map_zero, Poly.Raw.eval, zero_add, map_mul, Poly.C_mul]
      rw [ih, pow_succ]
      ring
    · simp only [List.zipIdx_cons, List.filterMap_cons, ha, ↓reduceIte, List.map_cons,
        Poly.Raw.eval, map_add, map_mul, Poly.C_mul, Poly.C_add]
      change Poly.C (f (K.lift a)) * (_ ^ start * _) + termsValue _ _ _ = _
      rw [ih, pow_succ]
      ring

private theorem eval_lift_coeffs (p : Poly (K R n)) :
    Poly.Raw.eval K.gen (p.coeffs.map K.lift) = K.joinPoly p := by
  rw [← Poly.Raw.eval_toPolynomial, Poly.Raw.toPolynomial_listMap, ← Poly.equiv_ofList,
    Poly.ofList_coeffs, Polynomial.eval_map]
  exact K.joinPolyHom_apply p

private theorem expansionValue (f : K R (n + 1) →+* F) (vs : List (Poly F))
    (ts : List (List ℕ × K R (n + 1))) (ps : List (Poly (K R n))) (d : K R (n + 1))
    (h : List.Forall₂ (fun x a => K.joinPoly a = x * d) (ts.map Prod.snd) ps) :
    termsValue (f.comp K.lift) (Poly.C (f K.gen) :: vs)
      ((ts.zip ps).flatMap fun ((m, _), p) =>
        p.coeffs.zipIdx.filterMap fun (a, i) => if a = 0 then none else some (i :: m, a)) =
      Poly.C (f d) * termsValue f vs ts := by
  induction ts generalizing ps with
  | nil =>
    cases h
    simp [termsValue]
  | cons t ts ih =>
    obtain ⟨m, c⟩ := t
    cases ps with
    | nil => cases h
    | cons p ps =>
      obtain ⟨hc, ht⟩ := List.forall₂_cons.mp h
      rw [List.zip_cons_cons, List.flatMap_cons, termsValue_append, expandedValue, ih _ ht,
        eval_lift_coeffs, pow_zero, mul_one, hc, map_mul, Poly.C_mul]
      change _ = Poly.C (f d) * (Poly.C (f c) * monomialValue vs m + termsValue f vs ts)
      ring

/-- Clearing every lower denominator multiplies the input by one nonzero scalar, independent
of the main variable. The assertion holds after every embedding of its coefficient field. -/
theorem clearTerms_value {k : ℕ} (f : K R k →+* F) (vs : List (Poly F))
    (ts : List (List ℕ × K R k)) : ∃ d : F, d ≠ 0 ∧
      termsValue (descend f) (parameters f vs) (clearTerms ts) =
        Poly.C d * termsValue f vs ts := by
  induction k generalizing vs with
  | zero => exact ⟨1, one_ne_zero, by simp [descend, parameters, clearTerms]⟩
  | succ k ih =>
    let d := K.joinPoly (commonDen (ts.map Prod.snd)).2
    have hc := commonDen_numerators (ts.map Prod.snd)
    unfold clearTerms
    dsimp only
    obtain ⟨b, hb, h⟩ := ih (f.comp K.lift) (Poly.C (f K.gen) :: vs) _
    change ∃ z : F, z ≠ 0 ∧ termsValue (descend (f.comp K.lift)) _ _ = _
    refine ⟨b * f d, mul_ne_zero hb ((map_ne_zero_iff f f.injective).mpr hc.1), ?_⟩
    change termsValue _ (parameters (f.comp K.lift) (Poly.C (f K.gen) :: vs)) _ = _
    rw [h, expansionValue _ _ _ _ d hc.2, Poly.C_mul, mul_assoc]

private theorem mainVariableValue (cs : List (K R n)) (start : ℕ) :
    termsValue (RingHom.id (K R n)) [Poly.X]
      ((cs.zipIdx start).filterMap fun (a, i) => if a = 0 then none else some ([i], a)) =
      Poly.X ^ start * Poly.ofList cs := by
  induction cs generalizing start with
  | nil => simp [termsValue]
  | cons a cs ih =>
    have peel : Poly.ofList (a :: cs) = Poly.C a + Poly.X * Poly.ofList cs := by
      apply Poly.equiv.injective
      simp [Poly.Raw.toPolynomial_cons]
    by_cases ha : a = 0
    · simp only [List.zipIdx_cons, List.filterMap_cons, ha, ↓reduceIte]
      subst a
      rw [ih, peel, Poly.C_zero, zero_add, pow_succ, mul_assoc]
    · simp only [List.zipIdx_cons, List.filterMap_cons, ha, ↓reduceIte]
      change Poly.C a * (Poly.X ^ start * 1) + termsValue _ _ _ = _
      rw [ih, peel, pow_succ]
      ring

/-- The sparse polynomial supplied to Kronecker substitution represents a nonzero scalar
multiple of the input when its lower variables are restored as the original generators. -/
theorem clear_polynomial (p : Poly (K R n)) :
    let f := RingHom.id (K R n)
    let terms := p.coeffs.zipIdx.filterMap fun (a, i) => if a = 0 then none else some ([i], a)
    ∃ d : K R n, d ≠ 0 ∧
      termsValue (descend f) (parameters f [Poly.X]) (clearTerms terms) = Poly.C d * p := by
  obtain ⟨d, hd, he⟩ := clearTerms_value (RingHom.id (K R n)) [Poly.X]
    (p.coeffs.zipIdx.filterMap fun (a, i) => if a = 0 then none else some ([i], a))
  exact ⟨d, hd, by simpa only [mainVariableValue, pow_zero, one_mul, Poly.ofList_coeffs] using he⟩

end Factor

end SympyProofs.Calculus.Antiderivative
