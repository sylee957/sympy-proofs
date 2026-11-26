module

public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite
public import SympyProofs.Calculus.Antiderivative.Extension.Hermite
public import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Correctness of Hermite reduction over a field with a derivation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

open scoped Polynomial
open SympyProofs.Calculus.Antiderivative.Extension.Hermite

variable {F : Type} [Field F] [DecidableEq F]

/-- Extend the coefficient derivation by prescribing the derivative of the new indeterminate. -/
noncomputable def modelDerivative (D : Derivation ℤ F F) (dx : Poly F) : Derivation ℤ F[X] F[X] :=
  letI : Differential F := ⟨D⟩
  Differential.implicitDeriv (Poly.equiv dx)

/-- The chain rule on coefficient lists realizes the model derivation. -/
theorem polyDer_spec (D : Derivation ℤ F F) (dx p : Poly F) :
    Poly.equiv (polyDer D dx p) = modelDerivative D dx (Poly.equiv p) := by
  let : Differential F := ⟨D⟩
  have h : Poly.equiv (Poly.map D p) = Differential.mapCoeffs (Poly.equiv p) := by
    ext j
    rw [Poly.coeff_equiv, Poly.coeff_map D (map_zero D), Differential.coeff_mapCoeffs,
      Poly.coeff_equiv]
    rfl
  simp only [polyDer, map_add, map_mul, Poly.equiv_derivative, h]
  rfl

/-- The computed pair of Bézout coefficients represents the monic gcd. -/
theorem bezout_spec (a b : Poly F) :
    a * (bezout a b).1 + b * (bezout a b).2 = gcd a b := by
  simp only [bezout, EuclideanDomain.xgcdAux_val]
  exact (Poly.gcd_eq_gcd_ab a b).symm

/-- Dividing by the repeated part and multiplying back recovers the original polynomial. -/
theorem squarefreeParts_mul {q : Poly F} (hq : q ≠ 0) :
    (squarefreeParts q).2 * (squarefreeParts q).1 = q := by
  apply EuclideanDomain.mul_div_cancel' _ (gcd_dvd_left q q.derivative)
  simp [gcd_eq_zero_iff, hq]

/-- The cofactor of the gcd with the formal derivative is squarefree. -/
theorem squarefreeParts_spec {q : Poly F} (hq : q ≠ 0) :
    Squarefree (Poly.equiv (squarefreeParts q).1) := by
  apply squarefree_of_gcd ((map_ne_zero_iff _ Poly.equiv.injective).mpr hq)
    (by simpa using congrArg Poly.equiv (squarefreeParts_mul hq).symm)
  have h := congrArg Poly.equiv (bezout_spec q q.derivative)
  exact (show Poly.equiv (bezout q q.derivative).1 * Poly.equiv q +
    Poly.equiv (bezout q q.derivative).2 * (Poly.equiv q).derivative = _ by
      simpa [squarefreeParts, mul_comm] using h)

local notation "V" => fun (p : Poly F) => algebraMap F[X] (RatFunc F) (Poly.equiv p)

/-- Interpret the fraction of two computable polynomials in the rational function field. -/
noncomputable def fraction (a b : Poly F) : RatFunc F := V a / V b

/-- The partial fraction at the special power and the normal fraction recover the input. -/
theorem separatePole_spec (a q : Poly F) (k : ℕ) (hd : Poly.X ^ k ∣ q)
    (hc : IsCoprime (Poly.X ^ k) (q / Poly.X ^ k)) :
    let r := separatePole a q k
    fraction r.normalNum r.normalDen + fraction r.specialNum (Poly.X ^ k) = fraction a q := by
  dsimp only
  by_cases hk : k = 0
  · simp [separatePole, hk, fraction]
  let x : Poly F := Poly.X ^ k
  have hx : x ≠ 0 := by
    rw [← map_ne_zero_iff Poly.equiv Poly.equiv.injective]
    simp [x]
  have hqd : x * (q / x) = q := EuclideanDomain.mul_div_cancel' hx hd
  have hbez := bezout_spec x (q / x)
  have hg := normalize_eq_one.mpr ((gcd_isUnit_iff_isRelPrime ..).mpr hc.isRelPrime)
  rw [normalize_gcd] at hg
  rw [hg] at hbez
  have hbx := congrArg (fun p => V p) hbez
  have hq := congrArg (fun p => V p) hqd
  simp only [map_add, map_mul, map_one] at hbx hq
  have hxn : V x ≠ 0 := RatFunc.algebraMap_ne_zero ((map_ne_zero_iff _ Poly.equiv.injective).mpr hx)
  by_cases h0 : q = 0
  · subst q
    have hunit : IsUnit x := by simpa [x, isCoprime_zero_right] using hc
    have hk0 : k = 0 := by
      have hx' : IsUnit (Poly.equiv x) := hunit.map Poly.equiv
      simpa [x] using Polynomial.natDegree_eq_zero_of_isUnit hx'
    exact False.elim (hk hk0)
  have hdn : V (q / x) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    apply (map_ne_zero_iff _ Poly.equiv.injective).mpr
    exact right_ne_zero_of_mul (hqd ▸ h0)
  simp only [separatePole, ite_eq_right hk, fraction, map_mul]
  change (V a * V (bezout x (q / x)).1) / V (q / x) +
    (V a * V (bezout x (q / x)).2) / V x = V a / V q
  dsimp only at hxn hdn ⊢
  rw [← hq]
  field_simp
  linear_combination V a * hbx

/-- The derivative of the indicated rational summand by the quotient rule. -/
noncomputable def exactDerivative (D : Derivation ℤ F F) (dx : Poly F) (t : Poly F × Poly F) :
    RatFunc F :=
  fraction (polyDer D dx t.1 * t.2 - t.1 * polyDer D dx t.2) (t.2 * t.2)

/-- Every prime divisor of the first polynomial also divides the second. -/
def primesCovered (p q : Poly F) : Prop :=
  ∀ r : F[X], Prime r → r ∣ Poly.equiv p → r ∣ Poly.equiv q

/-- No prime factor of the polynomial divides its own derivative. -/
def normalFactors (D : Derivation ℤ F F) (dx s : Poly F) : Prop :=
  ∀ r : F[X], Prime r → r ∣ Poly.equiv s → ¬ r ∣ modelDerivative D dx r

private theorem equiv_parts_bezout (m : Poly F) :
    ∃ u v : F[X], u * Poly.equiv m + v * (Poly.equiv m).derivative =
      Poly.equiv (squarefreeParts m).2 := by
  refine ⟨Poly.equiv (bezout m m.derivative).1, Poly.equiv (bezout m m.derivative).2, ?_⟩
  simpa [mul_comm, squarefreeParts] using congrArg Poly.equiv (bezout_spec m m.derivative)

variable [CharZero F]

/-- A Hermite step removes an exact derivative and strictly lowers the degree of the repeated
denominator. Its remaining prime factors continue to divide the squarefree denominator. -/
theorem hermiteStep_spec (D : Derivation ℤ F F) (dx s a m : Poly F)
    (hs : Squarefree (Poly.equiv s)) (hn : normalFactors D dx s)
    (hr : primesCovered m s) (hm : 0 < m.natDegree) :
    let next := hermiteStep D dx s a m
    fraction a (s * m) = exactDerivative D dx (next.exactNum, m) +
      fraction next.numerator (s * next.repeated) ∧
      next.repeated.natDegree < m.natDegree ∧ next.repeated ≠ 0 ∧
        primesCovered next.repeated s := by
  let rad := (squarefreeParts m).1
  let g := (squarefreeParts m).2
  let e := -((s * polyDer D dx m) / m)
  let b := (bezout e rad).1
  let c := (bezout e rad).2
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hm
  have hm' := (map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hm₀
  have hmg : Poly.equiv m = Poly.equiv g * Poly.equiv rad := by
    simpa [g, rad] using congrArg Poly.equiv (squarefreeParts_mul hm₀).symm
  have hrad : Poly.equiv rad ≠ 0 := right_ne_zero_of_mul (hmg ▸ hm')
  obtain ⟨u, v, huv⟩ := equiv_parts_bezout m
  have hrad' := step_dvd_radical hr hm' hmg huv
  have hradS : Poly.equiv s = Poly.equiv rad * Poly.equiv (s / rad) := by
    rw [Poly.equiv_div, EuclideanDomain.mul_div_cancel' hrad hrad']
  have hE := step_dvd (modelDerivative D dx) hr hm'
  have he : Poly.equiv e * Poly.equiv m =
      -(Poly.equiv s * modelDerivative D dx (Poly.equiv m)) := by
    simp only [e, map_neg, Poly.equiv_div, map_mul, polyDer_spec, neg_mul]
    rw [mul_comm _ (Poly.equiv m), EuclideanDomain.mul_div_cancel' hm' hE]
  have hc := step_coprime (modelDerivative D dx) hs hn hr hm' hmg he
  have hc' : IsCoprime e rad := by simpa using hc.map Poly.equiv.symm.toRingHom
  have hunit := normalize_eq_one.mpr ((gcd_isUnit_iff_isRelPrime ..).mpr hc'.isRelPrime)
  have hbc : e * b + rad * c = 1 := (bezout_spec e rad).trans (by simpa using hunit)
  have hid : Poly.equiv (a * b) * Poly.equiv e + Poly.equiv (a * c) * Poly.equiv rad =
      Poly.equiv a := by
    rw [← map_mul, ← map_mul, ← map_add]
    apply congrArg
    linear_combination a * hbc
  have heq := step_identity (modelDerivative D dx) hm' hs.ne_zero hmg hradS he hid
  change fraction a (s * m) = exactDerivative D dx (a * b, m) +
    fraction (a * c - polyDer D dx (a * b) * (s / rad)) (s * g) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [fraction, exactDerivative, map_sub, map_mul, polyDer_spec] using heq
  · have hgd : Poly.equiv g ∣ (Poly.equiv m).derivative := by
      simpa [g, squarefreeParts] using map_dvd Poly.equiv (gcd_dvd_right m m.derivative)
    simpa [g, hermiteStep] using step_degree (by simpa using hm) hgd
  · exact left_ne_zero_of_mul ((squarefreeParts_mul hm₀) ▸ hm₀)
  · intro p hp hp'
    apply hr p hp
    rw [hmg]
    exact hp'.mul_right _

omit [CharZero F] in
private theorem associated_at_constant (s m : Poly F) (hm : m ≠ 0) (hd : m.natDegree = 0) :
    Associated (Poly.equiv (s * m)) (Poly.equiv s) := by
  rw [map_mul]
  apply associated_mul_unit_left
  apply Polynomial.isUnit_iff_degree_eq_zero.mpr
  rw [Polynomial.degree_eq_natDegree ((map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hm)]
  simp [hd]

/-- Repeated reduction accounts for the derivative of every extracted term and leaves a
denominator associated to the squarefree part when the fuel covers the repeated degree. -/
theorem hermiteLoop_spec (D : Derivation ℤ F F) (dx s : Poly F) (hs : Squarefree (Poly.equiv s))
    (hn : normalFactors D dx s) (fuel : ℕ) (a m : Poly F) (hm : m ≠ 0)
    (hr : primesCovered m s) (hf : m.natDegree ≤ fuel) :
    let out := hermiteLoop D dx s fuel a m
    fraction a (s * m) = (out.exactTerms.map (exactDerivative D dx)).sum +
      fraction out.numerator out.denominator ∧
      Associated (Poly.equiv out.denominator) (Poly.equiv s) := by
  dsimp only
  induction fuel generalizing a m with
  | zero => simpa [hermiteLoop] using associated_at_constant s m hm (by omega)
  | succ k ih =>
    by_cases hd : m.natDegree = 0
    · simpa [hermiteLoop, hd] using associated_at_constant s m hm hd
    · obtain ⟨h, hdeg, hne, hrad⟩ := hermiteStep_spec D dx s a m hs hn hr (by omega)
      obtain ⟨heq, hass⟩ := ih _ _ hne hrad (by omega)
      refine ⟨?_, ?_⟩
      · simp only [hermiteLoop, ite_eq_right hd, List.map_cons, List.sum_cons]
        rw [h, heq, add_assoc]
      · simpa only [hermiteLoop, ite_eq_right hd] using hass

/-- Hermite reduction expresses a fraction as exact derivatives plus a fraction with
squarefree denominator dividing the original denominator, whenever its factors are normal. -/
theorem hermite_spec (D : Derivation ℤ F F) (dx a q : Poly F) (hn : normalFactors D dx q) :
    let out := hermite D dx a q
    fraction a q = (out.exactTerms.map (exactDerivative D dx)).sum +
      fraction out.numerator out.denominator ∧
      Squarefree (Poly.equiv out.denominator) ∧ Poly.equiv out.denominator ∣ Poly.equiv q := by
  dsimp only
  by_cases hq : q = 0
  · simp [hermite, hq, fraction]
  let s := (squarefreeParts q).1
  let m := (squarefreeParts q).2
  have hmg : m * s = q := squarefreeParts_mul hq
  have hmq : Poly.equiv q = Poly.equiv m * Poly.equiv s := by
    simpa using congrArg Poly.equiv hmg.symm
  have hd : Poly.equiv m ∣ (Poly.equiv q).derivative := by
    simpa [m, squarefreeParts] using map_dvd Poly.equiv (gcd_dvd_right q q.derivative)
  have hm : m ≠ 0 := left_ne_zero_of_mul (hmg ▸ hq)
  have hr : primesCovered m s := by
    intro p hp h
    exact prime_dvd_of_gcd ((map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hq) hmq hd hp
      (hmq ▸ h.mul_right _)
  have hs := squarefreeParts_spec hq
  have hsQ : Poly.equiv s ∣ Poly.equiv q := by rw [hmq]; exact dvd_mul_left _ _
  have hn' : normalFactors D dx s := fun p hp h => hn p hp (h.trans hsQ)
  obtain ⟨h, hass⟩ := hermiteLoop_spec D dx s hs hn' m.natDegree a m hm hr le_rfl
  simp only [hermite, ite_eq_right hq]
  exact ⟨by simpa only [mul_comm s m, hmg] using h, hass.squarefree_iff.mpr hs, hass.dvd.trans hsQ⟩

end SympyProofs.Calculus.Antiderivative.Step
