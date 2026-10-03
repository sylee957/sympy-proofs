import SympyProofs.RouthHurwitz.Exact.Domain

/-! Exact quotient backend for polynomial rings, by leading-term cancellation.
Iteration is bounded by the numerator degree. The noncomputable annotation comes
from mathlib's polynomial ring operations; the algorithm does not choose witnesses. -/
namespace RouthHurwitz.Exact
open Polynomial
variable {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A]

noncomputable def polynomialQuotient : ℕ → Polynomial A → Polynomial A → Polynomial A
  | 0, _, _ => 0
  | fuel+1, p, d =>
    if p = 0 then 0 else
    if p.natDegree < d.natDegree then 0 else
    let term := monomial (p.natDegree-d.natDegree) (p.leadingCoeff / d.leadingCoeff)
    term + polynomialQuotient fuel (p-d*term) d

omit [IsDomain A] [MulDivCancelClass A] in
private theorem polynomialQuotient_zero (fuel : ℕ) (d : Polynomial A) :
    polynomialQuotient fuel 0 d = 0 := by cases fuel <;> simp [polynomialQuotient]

private theorem polynomialQuotient_mul (fuel : ℕ) (a d : Polynomial A)
    (hd : d ≠ 0) (hf : a = 0 ∨ a.natDegree < fuel) :
    polynomialQuotient fuel (d*a) d = a := by
  induction fuel generalizing a with
  | zero =>
    have ha : a = 0 := hf.resolve_right (by omega)
    simp [ha, polynomialQuotient]
  | succ fuel ih =>
    by_cases ha : a = 0
    · simp [ha, polynomialQuotient_zero]
    have hdeg := natDegree_mul hd ha
    have hlt : ¬ (d*a).natDegree < d.natDegree := by omega
    have hterm : monomial ((d*a).natDegree-d.natDegree)
        ((d*a).leadingCoeff / d.leadingCoeff) = monomial a.natDegree a.leadingCoeff := by
      rw [hdeg, Nat.add_sub_cancel_left, leadingCoeff_mul,
        mul_div_cancel_left₀ _ (leadingCoeff_ne_zero.mpr hd)]
    rw [polynomialQuotient, if_neg (mul_ne_zero hd ha), if_neg hlt, hterm]
    have hrem : d*a-d*monomial a.natDegree a.leadingCoeff = d*a.eraseLead := by
      rw [← mul_sub, self_sub_monomial_natDegree_leadingCoeff]
    dsimp only
    rw [hrem, ih]
    · simp [add_comm, eraseLead_add_monomial_natDegree_leadingCoeff]
    · by_cases hz : a.eraseLead = 0
      · exact Or.inl hz
      · right
        have hh := natDegree_lt_natDegree hz (degree_eraseLead_lt ha)
        have := hf.resolve_left ha
        omega

/-- Polynomial division by leading-term cancellation. Scoped and lower priority
than Mathlib's field-coefficient division. Open `RouthHurwitz.Exact` to use it. -/
noncomputable scoped instance (priority := 100) polynomialDiv : Div (Polynomial A) where
  div p d := polynomialQuotient (p.natDegree+1) p d

/-- Exact cancellation for the specific polynomial division backend. -/
scoped instance polynomialMulDivCancelClass :
    @MulDivCancelClass (Polynomial A) _ polynomialDiv where
  mul_div_cancel a d hd := by
    change polynomialQuotient ((a*d).natDegree+1) (a*d) d = a
    rw [mul_comm a d]
    apply polynomialQuotient_mul _ _ _ hd
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [natDegree_mul hd ha]
      omega

/-- Transport a division operation along a ring equivalence. -/
@[reducible] def divOfEquiv {B : Type*} [CommRing B] [Div B]
    (e : A ≃+* B) : Div A where
  div a d := e.symm (e a / e d)

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
/-- Cancellation is preserved by the transported division operation. -/
theorem mulDivCancelOfEquiv {B : Type*} [CommRing B] [Div B] [MulDivCancelClass B]
    (e : A ≃+* B) : @MulDivCancelClass A _ (divOfEquiv e) := by
  refine @MulDivCancelClass.mk A _ (divOfEquiv e) ?_
  intro a d hd
  change e.symm (e (a*d) / e d) = a
  rw [map_mul, mul_div_cancel_right₀ _ (by simpa using hd), e.symm_apply_apply]

/-- Multivariate division via iterated univariate leading-term cancellation. -/
@[reducible] noncomputable def mvPolynomialDiv : (n : ℕ) → Div (MvPolynomial (Fin n) A)
  | 0 => divOfEquiv (MvPolynomial.isEmptyRingEquiv A (Fin 0))
  | n+1 =>
    letI : Div (MvPolynomial (Fin n) A) := mvPolynomialDiv n
    divOfEquiv (MvPolynomial.finSuccEquiv A n).toRingEquiv

/-- Exact cancellation for the specific multivariate backend. -/
theorem mvPolynomialMulDivCancelClass (n : ℕ) :
    @MulDivCancelClass (MvPolynomial (Fin n) A) _ (mvPolynomialDiv n) := by
  induction n with
  | zero => exact mulDivCancelOfEquiv (MvPolynomial.isEmptyRingEquiv A (Fin 0))
  | succ n ih =>
    letI : Div (MvPolynomial (Fin n) A) := mvPolynomialDiv n
    letI : MulDivCancelClass (MvPolynomial (Fin n) A) := ih
    letI : Div (Polynomial (MvPolynomial (Fin n) A)) := polynomialDiv
    have h : MulDivCancelClass (Polynomial (MvPolynomial (Fin n) A)) :=
      @polynomialMulDivCancelClass (MvPolynomial (Fin n) A) _ _ _ (mvPolynomialDiv n) ih
    exact @mulDivCancelOfEquiv _ _ _ _ (polynomialDiv (A := MvPolynomial (Fin n) A)) h
      (MvPolynomial.finSuccEquiv A n).toRingEquiv

attribute [scoped instance 100] mvPolynomialDiv
attribute [scoped instance] mvPolynomialMulDivCancelClass

end RouthHurwitz.Exact
