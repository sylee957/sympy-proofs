module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Decode
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.Ring

/-! Kronecker substitution is multiplicative, and decoding is exact on partially bounded inputs. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]

/-- The weight of coordinate i is the product of all preceding radices. -/
theorem encode_ofFn (bs : List ℕ) (e : Fin bs.length → ℕ) :
    encode bs (List.ofFn e) = ∑ i, (bs.take i.val).prod * e i := by
  induction bs with
  | nil => simp [encode, placeDigits]
  | cons b bs ih =>
    change _ = ∑ i : Fin (bs.length + 1), ((b :: bs).take i.val).prod * e i
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    change e 0 + b * encode bs (List.ofFn fun i => e i.succ) = _
    rw [ih, Finset.mul_sum]
    simp [List.take_succ_cons, mul_assoc]

/-- The value of a finite exponent function is the product of the variable powers. -/
theorem monomialValue_ofFn (vs : List (Poly G)) {k : ℕ} (e : Fin k → ℕ) :
    monomialValue vs (List.ofFn e) = ∏ i, (vs.getD i.val 1) ^ e i := by
  induction k generalizing vs with
  | zero => cases vs <;> simp [monomialValue]
  | succ k ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    cases vs with
    | nil => simp [monomialValue]
    | cons v vs =>
      rw [monomialValue, ih]
      simp

/-- The algebraic substitution corresponding to the executable monomial encoding. -/
noncomputable def substituteHom (bs : List ℕ) (k : ℕ) :
    MvPolynomial (Fin k) F →+* Poly F :=
  MvPolynomial.eval₂Hom Poly.CRingHom fun i => Poly.X ^ (bs.take i.val).prod

/-- Restore each parameter and keep the highest parameter as the formal variable. -/
noncomputable def restoreHom (f : F →+* G) (vs : List (Poly G)) (k : ℕ) :
    MvPolynomial (Fin k) F →+* Poly G :=
  MvPolynomial.eval₂Hom (Poly.CRingHom.comp f) fun i => vs.getD i.val 1

theorem substituteHom_monomial (bs : List ℕ) {k : ℕ} (hl : bs.length = k)
    (e : Fin k →₀ ℕ) (a : F) :
    substituteHom bs k (MvPolynomial.monomial e a) = Poly.monomial (encode bs (List.ofFn e)) a := by
  subst k
  rw [substituteHom, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, ← encode_ofFn bs e]
  apply Poly.equiv.injective
  simp [Polynomial.C_mul_X_pow_eq_monomial]

omit [DecidableEq F] in
theorem restoreHom_monomial (f : F →+* G) (vs : List (Poly G)) {k : ℕ}
    (e : Fin k →₀ ℕ) (a : F) :
    restoreHom f vs k (MvPolynomial.monomial e a) =
      Poly.C (f a) * monomialValue vs (List.ofFn e) := by
  rw [restoreHom, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp),
    monomialValue_ofFn]
  rfl

/-- Additive decoding of the substituted univariate polynomial. -/
private def decodeAddHom (f : F →+* G) (vs : List (Poly G)) (bs : List ℕ) :
    Poly F →+ Poly G where
  toFun := decode f vs bs
  map_zero' := by simp [decode]
  map_add' := decode_add f vs bs

/-- Decoding the substitution of a polynomial recovers precisely its evaluation in the
original variables if its degree in each variable is below that variable's radix. -/
theorem decode_substituteHom (f : F →+* G) (vs : List (Poly G)) (bs : List ℕ)
    {k : ℕ} (hl : bs.length = k) (p : MvPolynomial (Fin k) F)
    (bound : ∀ i : Fin k, p.degreeOf i < bs.getD i.val 0) :
    decode f vs bs (substituteHom bs k p) = restoreHom f vs k p := by
  change decodeAddHom f vs bs (substituteHom bs k p) = _
  conv_lhs => rw [p.as_sum, map_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  change decode f vs bs (substituteHom bs k _) = _
  rw [substituteHom_monomial bs hl, restoreHom_monomial, decode_monomial, decodeTerm, encode]
  have hb : List.Forall₂ (· < ·) (List.ofFn e) bs := by
    apply List.forall₂_of_length_eq_of_get (by simp [hl])
    intro i h₁ h₂
    have hi : i < k := by simpa using h₁
    have less := lt_of_le_of_lt (MvPolynomial.le_degreeOf_of_mem_support (⟨i,hi⟩ : Fin k) he)
      (bound ⟨i,hi⟩)
    simpa [List.getD_eq_getElem?_getD, h₂] using less
  rw [digits_place hb]

omit [DecidableEq F] in
/-- Every divisor of a nonzero partially bounded polynomial inherits the same bounds. -/
theorem bounds_of_dvd {k : ℕ} {p q : MvPolynomial (Fin k) F} (hp : p ≠ 0) (hd : q ∣ p)
    (bs : List ℕ) (bounds : ∀ i : Fin k, p.degreeOf i < bs.getD i.val 0) :
    ∀ i : Fin k, q.degreeOf i < bs.getD i.val 0 := by
  obtain ⟨r, hr⟩ := hd
  have hqr := mul_ne_zero_iff.mp (fun e => hp (hr.trans e))
  intro i
  have h := bounds i
  rw [hr, MvPolynomial.degreeOf_mul_eq hqr.1 hqr.2] at h
  omega

end SympyProofs.Calculus.Antiderivative.Factor
