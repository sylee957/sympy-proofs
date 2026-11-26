module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Basic
public import SympyProofs.Calculus.Antiderivative.Algebra.K.PartialRaw
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Variables
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The quotient rule on fractions and the derivation with prescribed generator derivatives. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K

section QuotientRule

variable {S A F : Type*} [CommRing S] [CommRing A] [Algebra S A] [Field F]
variable (ι : A →+* F) (D : Derivation S A A)

/-- The value of the quotient rule after embedding the coefficient ring in a field. -/
def quotientRule (a b : A) : F :=
  (ι (D a) * ι b - ι a * ι (D b)) / (ι b) ^ 2

private theorem quotientRule_zero (hι : Function.Injective ι) (a b : A)
    (h : ι a / ι b = 0) : quotientRule ι D a b = 0 := by
  rcases div_eq_zero_iff.mp h with ha | hb
  · have h := hι (ha.trans ι.map_zero.symm)
    simp [quotientRule, h]
  · simp [quotientRule, hb]

/-- The quotient rule depends only on the value of the fraction, including zero. -/
theorem quotientRule_congr (hι : Function.Injective ι) {a b c d : A}
    (h : ι a / ι b = ι c / ι d) : quotientRule ι D a b = quotientRule ι D c d := by
  by_cases hz : ι a / ι b = 0
  · rw [quotientRule_zero ι D hι a b hz, quotientRule_zero ι D hι c d (h ▸ hz)]
  have hb := (div_ne_zero_iff.mp hz).2
  have hd := (div_ne_zero_iff.mp (h ▸ hz)).2
  have hc := (div_eq_div_iff hb hd).mp h
  have hA : a * d = c * b := hι (by simpa using hc)
  have hD := congrArg (fun x => ι (D x)) hA
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hD
  unfold quotientRule
  apply (div_eq_div_iff (pow_ne_zero 2 hb) (pow_ne_zero 2 hd)).mpr
  linear_combination ι b * ι d * hD - (ι (D b) * ι d + ι b * ι (D d)) * hc

end QuotientRule

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [Div R] [NormalizedGCDMonoid R]
variable {n : ℕ}

/-- The value of a raw partial derivative is the quotient rule in the model field. -/
theorem value_pderiv (i : Fin n) (x : Raw R) :
    Raw.value n (Raw.pderiv n i x) =
      quotientRule (algebraMap _ (FractionRing (MvPolynomial (Fin n) R))) (MvPolynomial.pderiv i)
        (MPoly.Raw.toMvPolynomial n x.num) (MPoly.Raw.toMvPolynomial n x.den) := by
  unfold Raw.pderiv
  split
  · rename_i h
    have hden : MPoly.Raw.toMvPolynomial n x.den = 1 := by
      apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Fin n) R))
      simpa [Raw.polyEq_iff, Raw.polyValue] using h
    simp [quotientRule, hden, Raw.polyValue]
  · simp [quotientRule, MPoly.Raw.sub, Raw.polyValue, pow_two, sub_eq_add_neg]

private theorem value_pderiv_outside (i : ℕ) (hi : n ≤ i) (x : Raw R) :
    Raw.value n (Raw.pderiv n i x) = 0 := by
  unfold Raw.pderiv
  split <;> simp [MPoly.Raw.partial, Nat.not_lt.mpr hi, MPoly.Raw.sub, Raw.polyValue]

/-- The partial derivative of a flat fraction with respect to the given variable. -/
def pderiv (i : ℕ) : K R n → K R n :=
  Quotient.lift (s := Raw.setoid R n) (fun x => ofRaw (Raw.pderiv n i x)) fun x y h => by
    apply toFractionRing_injective
    simp only [toFractionRing_ofRaw]
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      rw [value_pderiv j, value_pderiv j]
      exact quotientRule_congr _ _ (IsFractionRing.injective _ _) h
    · simp [value_pderiv_outside i (Nat.le_of_not_lt hi)]

/-- On a representative, partial differentiation is the flat quotient rule. -/
@[simp] theorem pderiv_ofRaw (i : ℕ) (x : Raw R) :
    pderiv i (ofRaw x : K R n) = ofRaw (Raw.pderiv n i x) := rfl

/-- The partial derivative of a polynomial fraction satisfies the quotient rule. -/
theorem pderiv_div_ofPoly (i : Fin n) (a b : MPoly n R) :
    pderiv i (ofPoly a / ofPoly b) =
      (ofPoly (MPoly.pderiv i a) * ofPoly b - ofPoly a * ofPoly (MPoly.pderiv i b)) /
        ofPoly b ^ 2 := by
  let x : Raw R := ⟨a.terms, b.terms⟩
  have hx : ofRaw x = ofPoly a / ofPoly b := by rw [ofRaw_eq_div]; simp [x]
  rw [← hx, pderiv_ofRaw]
  apply equiv.injective
  simp only [equiv_ofRaw, value_pderiv i, map_div₀, map_sub, map_mul, map_pow, equiv_ofPoly,
    MPoly.equiv_pderiv]
  simp [quotientRule, x, ← MPoly.equiv_ofRaw]

/-- Variables beyond the height make no contribution to the derivative. -/
theorem pderiv_outside (i : ℕ) (hi : n ≤ i) (x : K R n) : pderiv i x = 0 := by
  induction x using Quotient.inductionOn with
  | _ a =>
    apply toFractionRing_injective
    exact (value_pderiv_outside i hi a).trans toFractionRing_zero.symm

private theorem exists_ofPoly_div (x : K R n) :
    ∃ a b : MPoly n R, ofPoly b ≠ 0 ∧ ofPoly a / ofPoly b = x := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (MPoly n R) x
  refine ⟨a, b, ?_, hx⟩
  change algebraMap (MPoly n R) (K R n) b ≠ 0
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

/-- Partial differentiation of flat fractions is additive. -/
theorem pderiv_add (i : ℕ) (x y : K R n) : pderiv i (x + y) = pderiv i x + pderiv i y := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    obtain ⟨a, b, hb, rfl⟩ := exists_ofPoly_div x
    obtain ⟨c, d, hd, rfl⟩ := exists_ofPoly_div y
    have h : ofPoly a / ofPoly b + ofPoly c / ofPoly d =
        ofPoly (a * d + b * c) / ofPoly (b * d) := by simp [div_add_div _ _ hb hd]
    rw [h, pderiv_div_ofPoly j, pderiv_div_ofPoly j, pderiv_div_ofPoly j]
    simp only [MPoly.pderiv_add, MPoly.pderiv_mul, map_add, map_mul]
    field_simp
    ring
  · simp [pderiv_outside i (Nat.le_of_not_lt hi)]

/-- Partial differentiation of flat fractions satisfies the product rule. -/
theorem pderiv_mul (i : ℕ) (x y : K R n) :
    pderiv i (x * y) = pderiv i x * y + x * pderiv i y := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    obtain ⟨a, b, hb, rfl⟩ := exists_ofPoly_div x
    obtain ⟨c, d, hd, rfl⟩ := exists_ofPoly_div y
    have h : ofPoly a / ofPoly b * (ofPoly c / ofPoly d) =
        ofPoly (a * c) / ofPoly (b * d) := by simp [div_mul_div_comm]
    rw [h, pderiv_div_ofPoly j, pderiv_div_ofPoly j, pderiv_div_ofPoly j]
    simp only [MPoly.pderiv_mul, map_add, map_mul]
    field_simp
    ring
  · simp [pderiv_outside i (Nat.le_of_not_lt hi)]

/-- Sum the remaining partial derivatives, starting at generator `i`. -/
def weightedPartials (x : K R n) (i : ℕ) : List (K R n) → K R n
  | [] => 0
  | v :: vs =>
    let rest := weightedPartials x (i + 1) vs
    if v = 0 then rest
    else if v = 1 then pderiv i x + rest else v * pderiv i x + rest

/-- View a raw polynomial as a fraction with denominator one. -/
def polynomial (p : MPoly.Raw R) : K R n := ofRaw (Raw.ofPoly p)

private theorem equiv_polynomial (p : MPoly.Raw R) :
    equiv (polynomial p : K R n) = Raw.polyValue n p := Raw.value_ofPoly n p

private theorem pderiv_ofRaw_rule (i : ℕ) (x : Raw R) :
    pderiv i (ofRaw x : K R n) =
      (polynomial (MPoly.Raw.partial n i x.num) * polynomial x.den -
        polynomial x.num * polynomial (MPoly.Raw.partial n i x.den)) /
          (polynomial x.den * polynomial x.den) := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change pderiv j _ = (polynomial (MPoly.Raw.partial n j x.num) * polynomial x.den -
      polynomial x.num * polynomial (MPoly.Raw.partial n j x.den)) / _
    apply equiv.injective
    simp only [pderiv_ofRaw, equiv_ofRaw, value_pderiv j, map_div₀, map_sub, map_mul,
      equiv_polynomial, Raw.polyValue, quotientRule, pow_two, MPoly.Raw.toMvPolynomial_partial j]
  · apply equiv.injective
    simp [pderiv_outside i (Nat.le_of_not_lt hi), MPoly.Raw.partial, hi, equiv_polynomial]

/-- Sum the weighted partial derivatives of one polynomial before applying the quotient rule. -/
def weightedPoly (p : MPoly.Raw R) (i : ℕ) : List (K R n) → K R n
  | [] => 0
  | v :: vs =>
    let rest := weightedPoly p (i + 1) vs
    if v = 0 then rest
    else
      let d := polynomial (MPoly.Raw.partial n i p)
      if d = 0 then rest else if v = 1 then d + rest else v * d + rest

private theorem weightedPoly_cons (p : MPoly.Raw R) (i : ℕ) (v : K R n) (vs : List (K R n)) :
    weightedPoly p i (v :: vs) =
      v * polynomial (MPoly.Raw.partial n i p) + weightedPoly p (i + 1) vs := by
  rw [weightedPoly]
  split_ifs <;> simp [*]

/-- Split off the contribution of the first generator in a list of velocities. -/
theorem weightedPartials_cons (x : K R n) (i : ℕ) (v : K R n) (vs : List (K R n)) :
    weightedPartials x i (v :: vs) = v * pderiv i x + weightedPartials x (i + 1) vs := by
  rw [weightedPartials]
  split_ifs <;> simp [*]

/-- Differentiate the numerator and denominator once and cancel one resulting fraction. -/
def differentiatePair (i : ℕ) (v : List (K R n)) (x : Raw R) : K R n :=
  match v with
  | [] => 0
  | _ :: _ =>
    let b := polynomial x.den
    (weightedPoly x.num i v * b - polynomial x.num * weightedPoly x.den i v) / (b * b)

private theorem differentiatePair_eq (i : ℕ) (v : List (K R n)) (x : Raw R) :
    differentiatePair i v x = weightedPartials (ofRaw x) i v := by
  induction v generalizing i with
  | nil => rfl
  | cons u us ih =>
    rw [weightedPartials_cons, ← ih, pderiv_ofRaw_rule]
    cases us with
    | nil =>
      simp only [differentiatePair, weightedPoly_cons]
      change ((_ + 0) * _ - _ * (_ + 0)) / _ = _ + 0
      simp only [add_zero, div_eq_mul_inv]
      ring
    | cons w ws =>
      simp only [differentiatePair, weightedPoly_cons, div_eq_mul_inv]
      ring

/-- The derivation sending each generator to its entry in the list. Missing entries are zero. -/
def der (v : List (K R n)) : K R n → K R n :=
  Quotient.lift (s := Raw.setoid R n) (differentiatePair 0 (v.take n)) fun a b h => by
    rw [differentiatePair_eq, differentiatePair_eq]
    exact congrArg (fun x => weightedPartials x 0 (v.take n)) (Quotient.sound h)

/-- The flat quotient rule is the sum of the weighted partial derivatives. -/
theorem der_eq_weightedPartials (v : List (K R n)) (x : K R n) :
    der v x = weightedPartials x 0 (v.take n) :=
  Quotient.inductionOn x (differentiatePair_eq 0 (v.take n))

/-- A polynomial viewed as a fraction has its polynomial partial derivative. -/
theorem pderiv_ofPoly (i : Fin n) (p : MPoly n R) :
    pderiv i (ofPoly p) = ofPoly (MPoly.pderiv i p) := by
  have ho : MPoly.pderiv i (1 : MPoly n R) = 0 := MPoly.equiv.injective (by simp)
  simpa [ho] using pderiv_div_ofPoly i p 1

/-- The partial derivative of a generator is its Kronecker delta. -/
theorem pderiv_ofPoly_X (i : ℕ) (j : Fin n) :
    pderiv i (ofPoly (MPoly.X j : MPoly n R)) = if i = j.val then 1 else 0 := by
  by_cases hi : i < n
  · let k : Fin n := ⟨i, hi⟩
    rw [pderiv_ofPoly k, MPoly.pderiv_X]
    by_cases h : k = j
    · simp [h, show i = j.val from congrArg Fin.val h]
    · simp [h, show i ≠ j.val from Fin.val_ne_of_ne h]
  · simp [pderiv_outside i (Nat.le_of_not_lt hi), show i ≠ j.val by omega]

/-- A sum of weighted partial derivatives is additive. -/
private theorem weighted_add (x y : K R n) (i : ℕ) (v : List (K R n)) :
    weightedPartials (x + y) i v = weightedPartials x i v + weightedPartials y i v := by
  induction v generalizing i with
  | nil => simp [weightedPartials]
  | cons u us ih =>
    simp only [weightedPartials_cons, pderiv_add, ih]
    ring

/-- A sum of weighted partial derivatives satisfies the product rule. -/
private theorem weighted_mul (x y : K R n) (i : ℕ) (v : List (K R n)) :
    weightedPartials (x * y) i v = weightedPartials x i v * y + x * weightedPartials y i v := by
  induction v generalizing i with
  | nil => simp [weightedPartials]
  | cons u us ih =>
    simp only [weightedPartials_cons, pderiv_mul, ih]
    ring

/-- The tower derivative preserves addition. -/
theorem der_add (v : List (K R n)) (x y : K R n) : der v (x + y) = der v x + der v y := by
  simp only [der_eq_weightedPartials, weighted_add]

/-- The tower derivative satisfies the product rule. -/
theorem der_mul (v : List (K R n)) (x y : K R n) :
    der v (x * y) = der v x * y + x * der v y := by
  simp only [der_eq_weightedPartials, weighted_mul]

/-- The tower derivative sends zero to zero. -/
@[simp] theorem der_zero (v : List (K R n)) : der v 0 = 0 := by
  simpa using (der_add v 0 0).symm

/-- The derivation with the prescribed generator derivatives as a Mathlib derivation. -/
def derivation (v : List (K R n)) : Derivation ℤ (K R n) (K R n) :=
  let f : K R n →+ K R n := ⟨⟨der v, der_zero v⟩, der_add v⟩
  Derivation.mk' f.toIntLinearMap fun x y => by
    change der v (x * y) = x * der v y + y * der v x
    rw [der_mul, add_comm, mul_comm (der v x)]

/-- The bundled derivation computes the flat quotient-rule derivative. -/
@[simp] theorem derivation_apply (v : List (K R n)) (x : K R n) : derivation v x = der v x := rfl

end SympyProofs.Calculus.Antiderivative.K
