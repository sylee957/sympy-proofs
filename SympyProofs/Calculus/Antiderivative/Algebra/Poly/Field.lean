module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

/-! Polynomials over a field: division with remainder, and what follows from it.

* `Poly.Raw`: the long division `Poly.Raw.divMod` of `Poly/Raw.lean` gives the same lists for
  lists that are the same polynomials (`divMod_congr`), and over a field its two parts are the
  quotient and the remainder of Mathlib's polynomials (`toPolynomial_divMod`).
* `/` and `%` on `Poly R` are the two parts of `divMod`, for any coefficients with a division.
* Over a field `F`, `Poly F` is a Euclidean domain with that quotient and that remainder
  (`equiv_div`, `equiv_mod`: they are Mathlib's), so the quotient of a multiple is exact
  (`MulDivCancelClass`). The greatest common divisor `EuclideanDomain.gcd` and the Bézout
  coefficients `EuclideanDomain.gcdA`, `gcdB` of Mathlib compute with them
  (`equiv_euclideanGcd`, `euclideanGcd_eq_gcd_ab`).
* `Poly F` has normalized greatest common divisors: `normalize p` is `p` divided by its
  leading coefficient (`normalize_eq_smul`), and `gcd p q` is `EuclideanDomain.gcd p q` made
  monic (`gcd_eq_normalize`, `leadingCoeff_gcd`, `gcd_eq_gcd_ab`, `associated_equiv_gcd`). -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open scoped Polynomial

namespace Poly.Raw

variable {R : Type}

/-! ### Long division respects the relation -/

section Congr

variable [Zero R] [Sub R] [Mul R] [Div R] [DecidableEq R]

/-- Long division gives the same two lists for lists that are the same polynomials. -/
theorem divMod_congr {p p' d d' : Raw R} (hp : Rel p p') (hd : Rel d d') :
    divMod p d = divMod p' d' := by
  rw [divMod, divMod, trim_congr hp, trim_congr hd]

end Congr

/-! ### Lists from the highest degree down -/

section Reverse

variable [CommRing R]

/-- The polynomial of two lists put end to end. -/
theorem toPolynomial_append (l m : Raw R) :
    toPolynomial (l ++ m) = toPolynomial l + Polynomial.X ^ l.length * toPolynomial m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, toPolynomial_cons, ih, List.length_cons]
    ring

/-- The polynomial of a list given from the highest degree down: its first element is the
coefficient of the highest degree. -/
theorem toPolynomial_reverse_cons (a : R) (l : Raw R) :
    toPolynomial (a :: l).reverse =
      toPolynomial l.reverse + Polynomial.C a * Polynomial.X ^ l.length := by
  rw [List.reverse_cons, toPolynomial_append, List.length_reverse]
  simp only [toPolynomial_cons, toPolynomial_nil, mul_zero, add_zero]
  ring

/-- The degree of the polynomial of a list is less than the length of the list. -/
theorem degree_toPolynomial_lt (l : Raw R) : (toPolynomial l).degree < l.length := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPolynomial, coeff_eq_zero_of_length_le hm]

/-- The degree of the polynomial of a list given from the highest degree down, when its first
element is not zero. -/
theorem degree_toPolynomial_reverse_cons {b : R} (hb : b ≠ 0) (d : Raw R) :
    (toPolynomial (b :: d).reverse).degree = d.length := by
  rw [toPolynomial_reverse_cons, Polynomial.degree_add_eq_right_of_degree_lt,
    Polynomial.degree_C_mul_X_pow _ hb]
  rw [Polynomial.degree_C_mul_X_pow _ hb]
  simpa using degree_toPolynomial_lt d.reverse

/-- One step of the long division keeps the length of what is left of the dividend. -/
theorem length_subMulAux (c : R) : ∀ p d : Raw R, (subMulAux c p d).length = p.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: p, _ :: d => by simp [subMulAux, length_subMulAux c p d]

/-- One step of the long division subtracts the multiple `c Xᵏ d` of the divisor, where `k` is
the difference of the lengths. -/
theorem toPolynomial_reverse_subMulAux (c : R) : ∀ p d : Raw R, d.length ≤ p.length →
    toPolynomial (subMulAux c p d).reverse =
      toPolynomial p.reverse -
        Polynomial.C c * Polynomial.X ^ (p.length - d.length) * toPolynomial d.reverse
  | [], [], _ => by simp [subMulAux]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], _ => by simp [subMulAux]
  | x :: p, y :: d, h => by
    have h' : d.length ≤ p.length := by simpa using h
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h'
    rw [subMulAux, toPolynomial_reverse_cons, toPolynomial_reverse_cons,
      toPolynomial_reverse_cons, length_subMulAux, toPolynomial_reverse_subMulAux c p d h']
    simp only [List.length_cons, Nat.add_sub_add_right, hn, Nat.add_sub_cancel_left, pow_add,
      map_sub, map_mul]
    ring

end Reverse

/-! ### Long division over a field is Mathlib's division -/

section Field

variable {F : Type} [Field F]

/-- A quotient and a remainder of smaller degree are the quotient and the remainder. -/
theorem div_mod_unique {P D Q S : F[X]} (hD : D ≠ 0) (h : Q * D + S = P)
    (hdeg : S.degree < D.degree) : Q = P / D ∧ S = P % D := by
  have hS : P % D = S := by
    rw [← h, Polynomial.add_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left D Q),
      (Polynomial.mod_eq_self_iff hD).mpr hdeg, zero_add]
  refine ⟨?_, hS.symm⟩
  have h2 := EuclideanDomain.div_add_mod P D
  rw [hS] at h2
  have h3 : Q * D = P / D * D := by
    rw [mul_comm (P / D) D]
    exact add_right_cancel (h.trans h2.symm)
  exact mul_right_cancel₀ hD h3

variable [DecidableEq F]

/-- What the loop of the long division keeps: the quotient found so far times the divisor,
plus what is left of the dividend, is the dividend. And what is left at the end is as long as
the divisor without its leading coefficient. -/
theorem divModAux_spec {b : F} (hb : b ≠ 0) (d : Raw F) : ∀ (k : ℕ) (p q : Raw F),
    p.length = k + d.length →
    toPolynomial (divModAux b d k p q).1 * toPolynomial (b :: d).reverse +
        toPolynomial (divModAux b d k p q).2.reverse =
      Polynomial.X ^ k * toPolynomial q * toPolynomial (b :: d).reverse +
        toPolynomial p.reverse ∧
    (divModAux b d k p q).2.length = d.length
  | 0, p, q, h => by simp [divModAux, h]
  | k + 1, [], q, h => by
    rw [List.length_nil] at h
    omega
  | k + 1, a :: p, q, h => by
    have hl : p.length = k + d.length := by
      rw [List.length_cons] at h
      omega
    have hab : Polynomial.C a = Polynomial.C (a / b) * Polynomial.C b := by
      rw [← map_mul, div_mul_cancel₀ _ hb]
    rw [divModAux]
    split_ifs with hc
    · obtain ⟨h1, h2⟩ := divModAux_spec hb d k p (a / b :: q) hl
      refine ⟨?_, h2⟩
      have hc' : a / b = 0 := by simpa using hc
      rw [h1, toPolynomial_cons, toPolynomial_reverse_cons a p, hab, hc']
      simp only [map_zero, zero_mul, zero_add, add_zero]
      ring
    · obtain ⟨h1, h2⟩ := divModAux_spec hb d k (subMulAux (a / b) p d) (a / b :: q)
        (by rw [length_subMulAux, hl])
      refine ⟨?_, h2⟩
      rw [h1, toPolynomial_reverse_subMulAux _ _ _ (by omega), toPolynomial_cons,
        toPolynomial_reverse_cons a p, toPolynomial_reverse_cons b d, hl, Nat.add_sub_cancel,
        hab]
      ring

/-- The two parts of the long division of lists are the quotient and the remainder of
Mathlib's polynomials. -/
theorem toPolynomial_divMod (p d : Raw F) :
    toPolynomial (divMod p d).1 = toPolynomial p / toPolynomial d ∧
      toPolynomial (divMod p d).2 = toPolynomial p % toPolynomial d := by
  have hp := toPolynomial_trim p
  have hd := toPolynomial_trim d
  have hlast := getLast?_trim d
  rw [divMod]
  cases hr : (trim d).reverse with
  | nil =>
    rw [List.reverse_eq_nil_iff] at hr
    rw [hr, toPolynomial_nil] at hd
    simp [← hd, hp]
  | cons b d' =>
    have htd : trim d = (b :: d').reverse := by rw [← hr, List.reverse_reverse]
    have hb : b ≠ 0 := by
      rw [htd] at hlast
      simpa using hlast
    rw [htd] at hd
    have hD : toPolynomial d ≠ 0 := by
      intro h0
      have := degree_toPolynomial_reverse_cons hb d'
      rw [hd, h0, Polynomial.degree_zero] at this
      exact absurd this (by simp)
    simp only [toPolynomial_trim]
    by_cases hlen : d'.length ≤ (trim p).length
    · obtain ⟨h1, h2⟩ := divModAux_spec hb d' ((trim p).length - d'.length) (trim p).reverse []
        (by rw [List.length_reverse]; omega)
      rw [List.reverse_reverse, hp, hd] at h1
      simp only [toPolynomial_nil, mul_zero, zero_mul, zero_add] at h1
      refine div_mod_unique hD h1 ?_
      rw [← hd, degree_toPolynomial_reverse_cons hb]
      simpa [h2] using degree_toPolynomial_lt (divModAux b d' ((trim p).length - d'.length)
        (trim p).reverse []).2.reverse
    · have hk : (trim p).length - d'.length = 0 := by omega
      rw [hk]
      simp only [divModAux, toPolynomial_nil, List.reverse_reverse, hp]
      refine div_mod_unique hD (by simp) ?_
      rw [← hd, degree_toPolynomial_reverse_cons hb, ← hp]
      exact (degree_toPolynomial_lt _).trans (by exact_mod_cast Nat.lt_of_not_le hlen)

end Field

end Poly.Raw

namespace Poly

variable {R : Type}

/-! ### Quotient and remainder -/

section Div

variable [Zero R] [Sub R] [Mul R] [Div R] [DecidableEq R]

/-- The quotient and the remainder of the long division, which divides by the leading
coefficient of the divisor. Division by zero gives the quotient zero and the remainder the
dividend. -/
def divMod (p d : Poly R) : Poly R × Poly R :=
  Quotient.lift₂ (s₁ := Raw.setoid R) (s₂ := Raw.setoid R)
    (fun l m => let r := Raw.divMod l m; (ofList r.1, ofList r.2))
    (fun _ _ _ _ hp hd => by rw [Raw.divMod_congr hp hd]) p d

/-- The quotient of the long division. -/
protected def div (p d : Poly R) : Poly R := (p.divMod d).1

/-- The remainder of the long division. -/
protected def mod (p d : Poly R) : Poly R := (p.divMod d).2

/-- The quotient of polynomials is the quotient of the long division of lists. -/
instance : Div (Poly R) := ⟨Poly.div⟩

/-- The remainder of polynomials is the remainder of the long division of lists. -/
instance : Mod (Poly R) := ⟨Poly.mod⟩

theorem divMod_ofList (l m : List R) :
    (ofList l).divMod (ofList m) = (ofList (Raw.divMod l m).1, ofList (Raw.divMod l m).2) := rfl

theorem ofList_div (l m : List R) : ofList l / ofList m = ofList (Raw.divMod l m).1 := rfl

theorem ofList_mod (l m : List R) : ofList l % ofList m = ofList (Raw.divMod l m).2 := rfl

/-- The two parts of the long division are the quotient and the remainder. -/
theorem divMod_eq (p d : Poly R) : p.divMod d = (p / d, p % d) := rfl

end Div

/-! ### The Euclidean domain -/

section Field

variable {F : Type} [Field F] [DecidableEq F]

/-- The quotient is the quotient of Mathlib's polynomials. -/
@[simp] theorem equiv_div (p q : Poly F) : equiv (p / q) = equiv p / equiv q := by
  induction p, q using induction_on₂ with
  | h l m => exact (Raw.toPolynomial_divMod l m).1

/-- The remainder is the remainder of Mathlib's polynomials. -/
@[simp] theorem equiv_mod (p q : Poly F) : equiv (p % q) = equiv p % equiv q := by
  induction p, q using induction_on₂ with
  | h l m => exact (Raw.toPolynomial_divMod l m).2

/-- Polynomials over a field are a Euclidean domain: the quotient and the remainder are those
of the long division, and the remainder has a smaller degree than the divisor. -/
instance : EuclideanDomain (Poly F) where
  __ := (inferInstance : CommRing (Poly F))
  __ := (inferInstance : Nontrivial (Poly F))
  quotient := Poly.div
  quotient_zero p := equiv.injective ((equiv_div p 0).trans (by simp))
  remainder := Poly.mod
  quotient_mul_add_remainder_eq p q := equiv.injective (by
    change equiv (q * (p / q) + p % q) = equiv p
    rw [map_add, map_mul, equiv_div, equiv_mod]
    exact EuclideanDomain.div_add_mod (equiv p) (equiv q))
  r p q := (equiv p).degree < (equiv q).degree
  r_wellFounded := InvImage.wf equiv Polynomial.degree_lt_wf
  remainder_lt p q hq := by
    change (equiv (p % q)).degree < (equiv q).degree
    rw [equiv_mod]
    exact Polynomial.degree_mod_lt _ ((map_ne_zero_iff equiv equiv.injective).mpr hq)
  mul_left_not_lt p q hq := by
    rw [map_mul]
    exact not_lt_of_ge (Polynomial.degree_le_mul_left _
      ((map_ne_zero_iff equiv equiv.injective).mpr hq))

/-- The remainder has a smaller degree than a divisor that is not constant. -/
theorem natDegree_mod_lt (p : Poly F) {q : Poly F} (hq : q.natDegree ≠ 0) :
    (p % q).natDegree < q.natDegree := by
  rw [← natDegree_equiv, ← natDegree_equiv, equiv_mod]
  exact Polynomial.natDegree_mod_lt _ (by rwa [natDegree_equiv])

/-- The quotient of a multiple by its factor is the other factor. Mathlib has this for every
Euclidean domain; it is stated here for the quotient of polynomials itself, so that it is
found without a search for the Euclidean domain inside the search. -/
instance : MulDivCancelClass (Poly F) := ⟨fun p _ hq => mul_div_cancel_right₀ p hq⟩

/-- The greatest common divisor of Mathlib's Euclidean algorithm is the one of Mathlib's
polynomials. -/
theorem equiv_euclideanGcd [DecidableEq F[X]] (p q : Poly F) :
    equiv (EuclideanDomain.gcd p q) = EuclideanDomain.gcd (equiv p) (equiv q) := by
  induction p, q using EuclideanDomain.GCD.induction with
  | H0 q => rw [EuclideanDomain.gcd_zero_left, map_zero, EuclideanDomain.gcd_zero_left]
  | H1 p q _ ih =>
    rw [EuclideanDomain.gcd_val, ih, equiv_mod, ← EuclideanDomain.gcd_val]

/-- The identity of Bézout for Mathlib's Euclidean algorithm: the greatest common divisor is a
combination of the two polynomials, with the coefficients `EuclideanDomain.gcdA` and
`EuclideanDomain.gcdB`, which compute. -/
theorem euclideanGcd_eq_gcd_ab (p q : Poly F) :
    EuclideanDomain.gcd p q =
      p * EuclideanDomain.gcdA p q + q * EuclideanDomain.gcdB p q :=
  EuclideanDomain.gcd_eq_gcd_ab p q

/-! ### Monic polynomials and greatest common divisors -/

/-- The unit by which a polynomial is multiplied to make it monic: the inverse of its leading
coefficient, and one for the zero polynomial. -/
protected def normUnit (p : Poly F) : (Poly F)ˣ :=
  if h : p.leadingCoeff = 0 then 1
  else ⟨C p.leadingCoeff⁻¹, C p.leadingCoeff, by rw [← C_mul, inv_mul_cancel₀ h, C_one],
    by rw [← C_mul, mul_inv_cancel₀ h, C_one]⟩

/-- The unit that makes a polynomial monic is the one of Mathlib's polynomials. -/
theorem equiv_coe_normUnit (p : Poly F) :
    equiv (p.normUnit : Poly F) = ↑(normUnit (equiv p)) := by
  rw [Polynomial.coe_normUnit, leadingCoeff_equiv, Poly.normUnit]
  split_ifs with h
  · simp [h]
  · simp [CommGroupWithZero.coe_normUnit _ h]

/-- Polynomials over a field are normalized by dividing by the leading coefficient. -/
instance : NormalizationMonoid (Poly F) where
  normUnit := Poly.normUnit
  normUnit_zero := by simp [Poly.normUnit]
  normUnit_one := Units.ext (equiv.injective (by
    rw [equiv_coe_normUnit]
    simp))
  normUnit_mul_units {a} u ha := Units.ext (equiv.injective (by
    have h := congrArg Units.val (normUnit_mul_units (Units.map equiv.toMonoidHom u)
      ((map_ne_zero_iff equiv equiv.injective).mpr ha))
    rw [Units.val_mul, map_mul, equiv_coe_normUnit, equiv_coe_normUnit, map_mul]
    simpa using h))

/-- The unit that makes a nonzero polynomial monic is the inverse of its leading
coefficient. -/
theorem coe_normUnit_of_ne_zero {p : Poly F} (hp : p ≠ 0) :
    (↑(normUnit p) : Poly F) = C p.leadingCoeff⁻¹ := by
  change (↑p.normUnit : Poly F) = _
  rw [Poly.normUnit]
  split_ifs with h
  · exact absurd h (leadingCoeff_ne_zero hp)
  · rfl

/-- Normalizing a polynomial divides it by its leading coefficient. -/
theorem normalize_eq_C_mul (p : Poly F) : normalize p = C p.leadingCoeff⁻¹ * p := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [normalize_apply, coe_normUnit_of_ne_zero hp, mul_comm]

/-- Normalizing a polynomial divides every coefficient by the leading coefficient. -/
theorem normalize_eq_smul (p : Poly F) : normalize p = p.leadingCoeff⁻¹ • p := by
  rw [normalize_eq_C_mul, C_mul_eq_smul]

/-- The coefficients of a normalized polynomial are the coefficients divided by the leading
coefficient. -/
@[simp] theorem coeff_normalize (p : Poly F) (n : ℕ) :
    (normalize p).coeff n = p.coeff n / p.leadingCoeff := by
  rw [normalize_eq_smul, coeff_smul, smul_eq_mul, div_eq_inv_mul]

/-- Normalizing is normalizing Mathlib's polynomial. -/
@[simp] theorem equiv_normalize (p : Poly F) : equiv (normalize p) = normalize (equiv p) := by
  rw [normalize_apply, map_mul, normalize_apply]
  exact congrArg _ (equiv_coe_normUnit p)

/-- A normalized polynomial is monic, or zero. -/
@[simp] theorem leadingCoeff_normalize (p : Poly F) :
    (normalize p).leadingCoeff = if p = 0 then 0 else 1 := by
  split_ifs with hp
  · simp [hp]
  · rw [← leadingCoeff_equiv, equiv_normalize, Polynomial.leadingCoeff_normalize,
      leadingCoeff_equiv, CommGroupWithZero.normalize_eq_one _ (leadingCoeff_ne_zero hp)]

/-- Normalizing does not change the degree. -/
@[simp] theorem natDegree_normalize (p : Poly F) : (normalize p).natDegree = p.natDegree := by
  rw [← natDegree_equiv, equiv_normalize, Polynomial.natDegree_normalize, natDegree_equiv]

/-- The normalized polynomials are the monic ones and zero. -/
theorem normalize_eq_self_iff {p : Poly F} : normalize p = p ↔ p = 0 ∨ p.leadingCoeff = 1 := by
  constructor
  · intro h
    by_cases hp : p = 0
    · exact Or.inl hp
    · right
      rw [← h, leadingCoeff_normalize]
      simp [hp]
  · rintro (rfl | h)
    · exact normalize_zero
    · rw [normalize_eq_C_mul, h, inv_one, C_one, one_mul]

/-- The product of normalized polynomials is normalized. -/
instance : StrongNormalizationMonoid (Poly F) where
  __ := (inferInstance : NormalizationMonoid (Poly F))
  normUnit_mul {a b} ha hb := Units.ext (equiv.injective (by
    have h := congrArg Units.val (normUnit_mul
      ((map_ne_zero_iff equiv equiv.injective).mpr ha)
      ((map_ne_zero_iff equiv equiv.injective).mpr hb))
    rw [Units.val_mul] at h
    change equiv ((a * b).normUnit : Poly F) =
      equiv ((a.normUnit : Poly F) * (b.normUnit : Poly F))
    rw [map_mul, equiv_coe_normUnit, equiv_coe_normUnit, equiv_coe_normUnit, map_mul, h]))
  normUnit_coe_units := normUnit_coe_units

/-- Polynomials over a field have greatest common divisors, and the chosen one is monic: it is
the result of Mathlib's Euclidean algorithm divided by its leading coefficient. The least
common multiple is the product divided by it, made monic. -/
instance : NormalizedGCDMonoid (Poly F) where
  __ := (inferInstance : NormalizationMonoid (Poly F))
  gcd p q := normalize (EuclideanDomain.gcd p q)
  lcm p q := normalize (EuclideanDomain.lcm p q)
  gcd_dvd_left p q := normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left p q)
  gcd_dvd_right p q := normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right p q)
  dvd_gcd hac hab := dvd_normalize_iff.mpr (EuclideanDomain.dvd_gcd hac hab)
  gcd_mul_lcm p q := by
    rw [← EuclideanDomain.gcd_mul_lcm p q]
    exact (normalize_associated _).mul_mul (normalize_associated _)
  lcm_zero_left p := by rw [EuclideanDomain.lcm_zero_left, normalize_zero]
  lcm_zero_right p := by rw [EuclideanDomain.lcm_zero_right, normalize_zero]
  normalize_gcd p q := normalize_idem _
  normalize_lcm p q := normalize_idem _

/-- The greatest common divisor is the one of Mathlib's Euclidean algorithm, made monic. -/
theorem gcd_eq_normalize (p q : Poly F) : gcd p q = normalize (EuclideanDomain.gcd p q) := rfl

/-- The least common multiple is the product divided by the greatest common divisor, made
monic. -/
theorem lcm_eq_normalize (p q : Poly F) : lcm p q = normalize (EuclideanDomain.lcm p q) := rfl

/-- The greatest common divisor is monic, or zero when both polynomials are. -/
@[simp] theorem leadingCoeff_gcd (p q : Poly F) :
    (gcd p q).leadingCoeff = if p = 0 ∧ q = 0 then 0 else 1 := by
  rw [gcd_eq_normalize, leadingCoeff_normalize]
  simp only [EuclideanDomain.gcd_eq_zero_iff]

/-- The greatest common divisor with a nonzero polynomial is monic. -/
theorem leadingCoeff_gcd_of_left_ne_zero {p : Poly F} (hp : p ≠ 0) (q : Poly F) :
    (gcd p q).leadingCoeff = 1 := by
  simp [hp]

/-- The greatest common divisor with a nonzero polynomial is monic. -/
theorem leadingCoeff_gcd_of_right_ne_zero (p : Poly F) {q : Poly F} (hq : q ≠ 0) :
    (gcd p q).leadingCoeff = 1 := by
  simp [hq]

/-- The identity of Bézout: the monic greatest common divisor is a combination of the two
polynomials. The coefficients are those of Mathlib's Euclidean algorithm divided by the
leading coefficient of its result. -/
theorem gcd_eq_gcd_ab (p q : Poly F) :
    gcd p q =
      p * (C (EuclideanDomain.gcd p q).leadingCoeff⁻¹ * EuclideanDomain.gcdA p q) +
        q * (C (EuclideanDomain.gcd p q).leadingCoeff⁻¹ * EuclideanDomain.gcdB p q) := by
  rw [gcd_eq_normalize, normalize_eq_C_mul]
  nth_rewrite 2 [EuclideanDomain.gcd_eq_gcd_ab p q]
  ring

/-- The greatest common divisor is the one of Mathlib's Euclidean algorithm on Mathlib's
polynomials, made monic. -/
theorem equiv_gcd [DecidableEq F[X]] (p q : Poly F) :
    equiv (gcd p q) = normalize (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  rw [gcd_eq_normalize, equiv_normalize, equiv_euclideanGcd]

/-- The greatest common divisor is a greatest common divisor of Mathlib's polynomials,
whichever is chosen there. -/
theorem associated_equiv_gcd [GCDMonoid F[X]] (p q : Poly F) :
    Associated (equiv (gcd p q)) (gcd (equiv p) (equiv q)) := by
  have h : equiv.symm (gcd (equiv p) (equiv q)) ∣ gcd p q :=
    dvd_gcd (by simpa using map_dvd equiv.symm (gcd_dvd_left (equiv p) (equiv q)))
      (by simpa using map_dvd equiv.symm (gcd_dvd_right (equiv p) (equiv q)))
  exact associated_of_dvd_dvd
    (dvd_gcd (map_dvd equiv (gcd_dvd_left p q)) (map_dvd equiv (gcd_dvd_right p q)))
    (by simpa using map_dvd equiv h)

end Field

end Poly

end SympyProofs.Calculus.Antiderivative
