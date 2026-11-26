module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Heights
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Reduced
public import SympyProofs.Calculus.Antiderivative.Algebra.K.SplitPolynomial

/-! Canonical polynomial numerator and denominator in the last generator of a flat field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K

open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Expand a sparse polynomial along its final coordinate, embedding each lower monomial. -/
def splitTerms (n : ℕ) : MPoly.Raw R → Poly (K R n)
  | [] => 0
  | (e,c) :: p =>
    if e.trim.length ≤ n + 1 then
      Poly.monomial (e.getD n 0) (ofPoly (MPoly.ofRaw [(e.take n, c)])) + splitTerms n p
    else splitTerms n p

/-- Reading each term's final exponent performs the last-variable isomorphism on polynomials. -/
theorem interpret_splitTerms (p : MPoly.Raw R) :
    Poly.interpret equiv (splitTerms n p) =
      (Model.splitPolynomial R n (MPoly.Raw.toMvPolynomial (n + 1) p)).map (algebraMap _ _) := by
  induction p with
  | nil => simp [splitTerms]
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    by_cases he : e.trim.length ≤ n + 1
    · have he' : (Mono.trim (e.take n)).length ≤ n := (Mono.fits_iff n _).mpr fun i hi =>
        Poly.Raw.coeff_eq_zero_of_length_le (le_trans (List.length_take_le ..) hi)
      rw [splitTerms, ite_eq_left he, map_add, ih, MPoly.Raw.toMvPolynomial_cons, ite_eq_left he,
        map_add, Polynomial.map_add, Model.splitPolynomial_monomial]
      simp [MPoly.Raw.toMvPolynomial_cons, he', Poly.Raw.coeff]
    · simp [splitTerms, he, MPoly.Raw.toMvPolynomial_cons, ← ih]

/-- The canonical univariate pair for an arbitrary representative, including a zero denominator. -/
def Raw.split (n : ℕ) (x : Raw R) : Poly (K R n) × Poly (K R n) :=
  Poly.reduced (splitTerms n x.num) (splitTerms n x.den)

/-- Splitting a raw representative computes the model's usual numerator and denominator. -/
theorem Raw.interpret_split (x : Raw R) :
    let z := Model.stepEquiv R n (Raw.value (n + 1) x)
    (Poly.interpret equiv (x.split n).1, Poly.interpret equiv (x.split n).2) =
      (z.num, z.denom) := by
  have h := Poly.interpret_reduced equiv (splitTerms n x.num) (splitTerms n x.den)
  dsimp only at h ⊢
  rw [Raw.value, map_div₀, Raw.polyValue, Raw.polyValue, Model.stepEquiv_polynomial,
    Model.stepEquiv_polynomial, ← interpret_splitTerms, ← interpret_splitTerms]
  exact h

theorem Raw.split_congr (a b : Raw R) (h : value (n + 1) a = value (n + 1) b) :
    a.split n = b.split n := by
  have ha := Raw.interpret_split (n := n) a
  have hb := Raw.interpret_split (n := n) b
  dsimp only at ha hb
  rw [h, ← hb] at ha
  have hc := Prod.mk.inj ha
  exact Prod.ext ((Poly.interpret (equiv (R := R) (n := n))).injective hc.1)
    ((Poly.interpret (equiv (R := R) (n := n))).injective hc.2)

/-- The canonical numerator and monic denominator as polynomials over the field below. -/
def split (x : K R (n + 1)) : Poly (K R n) × Poly (K R n) :=
  Quotient.lift (s := Raw.setoid R (n + 1)) (Raw.split n) Raw.split_congr x

/-- The returned pair is RatFunc's canonical pair in the last-variable model. -/
theorem interpret_split (x : K R (n + 1)) :
    let z := Model.stepEquiv R n (equiv x)
    (Poly.interpret equiv x.split.1, Poly.interpret equiv x.split.2) = (z.num, z.denom) :=
  Quotient.inductionOn x fun a => Raw.interpret_split a

/-- Evaluate a polynomial in the new generator, including its coefficients from below. -/
def joinPoly (p : Poly (K R n)) : K R (n + 1) :=
  (p.map lift).eval gen

/-- Evaluation in the new generator becomes the inclusion of polynomials in rational functions. -/
theorem stepEquiv_joinPoly (p : Poly (K R n)) :
    Model.stepEquiv R n (equiv (joinPoly p)) =
      algebraMap (M R n)[X] _ (Poly.interpret equiv p) := by
  rw [joinPoly, ← Poly.eval_equiv, Poly.equiv_map, Polynomial.eval_map, Poly.interpret_apply]
  generalize Poly.equiv p = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
  | monomial d a =>
    rw [Polynomial.eval₂_monomial, Polynomial.map_monomial,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, stepEquiv_lift, stepEquiv_gen, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X, RingEquiv.coe_toRingHom]

/-- Form the quotient of two polynomials in the newest generator. -/
def join (p q : Poly (K R n)) : K R (n + 1) := joinPoly p / joinPoly q

/-- Joining the canonical pair recovers the input field element. -/
@[simp] theorem join_split (x : K R (n + 1)) : join x.split.1 x.split.2 = x := by
  apply (equiv.trans (Model.stepEquiv R n)).injective
  change Model.stepEquiv R n (equiv (joinPoly _ / joinPoly _)) = _
  rw [map_div₀, map_div₀, stepEquiv_joinPoly, stepEquiv_joinPoly]
  obtain ⟨hn,hd⟩ := Prod.mk.inj (interpret_split x)
  rw [hn, hd, RatFunc.num_div_denom]
  rfl

end SympyProofs.Calculus.Antiderivative.K
