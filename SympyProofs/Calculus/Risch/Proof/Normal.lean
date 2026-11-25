module

public import SympyProofs.Calculus.Risch.Program.Normal
public import SympyProofs.Calculus.Risch.Spec.Field
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The comparison of terms decides equality in the field of a tower, over every constant
field of characteristic zero: the generators are algebraically independent there, so a
polynomial with rational coefficients vanishes on them only if it is zero. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : ℕ}

namespace MPoly

/-- The exponents of a monomial as a finitely supported function. -/
noncomputable def exps (m : Mono n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin n => m[i]

theorem exps_apply (m : Mono n) (i : Fin n) : exps m i = m[i] := rfl

theorem exps_injective : Function.Injective (exps (n := n)) := by
  intro m k h
  apply Vector.ext
  intro i hi
  have := congrArg (fun f : Fin n →₀ ℕ => f ⟨i, hi⟩) h
  simpa [exps_apply] using this

theorem exps_add (m k : Mono n) : exps (Vector.zipWith (· + ·) m k) = exps m + exps k := by
  ext i
  simp [exps_apply]

theorem exps_zero : exps (Vector.replicate n 0) = 0 := by
  ext i
  simp [exps_apply]

theorem exps_indet (i : Fin n) :
    exps (Vector.ofFn fun j => if i == j then 1 else 0) = Finsupp.single i 1 := by
  ext j
  simp [exps_apply, Finsupp.single_apply]

theorem exists_exps (f : Fin n →₀ ℕ) : ∃ m : Mono n, exps m = f :=
  ⟨Vector.ofFn f, by ext i; simp [exps_apply]⟩

/-- The polynomial a list of monomials denotes. -/
noncomputable def asPoly : MPoly n → MvPolynomial (Fin n) ℚ
  | [] => 0
  | (m, a) :: p => MvPolynomial.monomial (exps m) a + asPoly p

@[simp] theorem asPoly_nil : asPoly ([] : MPoly n) = 0 := rfl

theorem asPoly_cons (m : Mono n) (a : ℚ) (p : MPoly n) :
    asPoly ((m, a) :: p) = MvPolynomial.monomial (exps m) a + asPoly p := rfl

@[simp] theorem asPoly_scalar (a : ℚ) : asPoly (scalar a : MPoly n) = MvPolynomial.C a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [scalar]
  · have : (a == 0) = false := by simpa using ha
    simp only [scalar, this, Bool.false_eq_true, ite_false, asPoly_cons, asPoly_nil, add_zero,
      exps_zero]
    rfl

@[simp] theorem asPoly_indet (i : Fin n) : asPoly (indet i) = MvPolynomial.X i := by
  rw [indet, asPoly_cons, asPoly_nil, exps_indet, add_zero]
  rfl

theorem asPoly_addTerm (m : Mono n) (a : ℚ) (p : MPoly n) :
    asPoly (addTerm m a p) = MvPolynomial.monomial (exps m) a + asPoly p := by
  induction p with
  | nil =>
    by_cases ha : a = 0 <;> simp [addTerm, ha, asPoly_cons]
  | cons t p ih =>
    rcases t with ⟨k, b⟩
    by_cases he : m = k
    · subst k
      by_cases hz : a + b = 0
      · simp [addTerm, asPoly_cons, ← add_assoc, ← map_add, hz]
      · simp [addTerm, hz, asPoly_cons, map_add, add_assoc]
    · have : (m == k) = false := by simpa using he
      simp only [addTerm, this, Bool.false_eq_true, ite_false, asPoly_cons, ih, add_left_comm]

@[simp] theorem asPoly_add (p q : MPoly n) : asPoly (add p q) = asPoly p + asPoly q := by
  induction p with
  | nil => simp [add]
  | cons t p ih =>
    rcases t with ⟨m, c⟩
    simp [add, asPoly_addTerm, asPoly_cons, ih, add_assoc]

@[simp] theorem asPoly_neg (p : MPoly n) : asPoly (neg p) = -asPoly p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    rcases t with ⟨m, c⟩
    change MvPolynomial.monomial _ (-c) + asPoly (neg p) = -(MvPolynomial.monomial _ c + _)
    rw [ih, map_neg, neg_add_rev]
    exact add_comm _ _

theorem asPoly_mulTerm (m : Mono n) (a : ℚ) (p : MPoly n) :
    asPoly (mulTerm m a p) = MvPolynomial.monomial (exps m) a * asPoly p := by
  induction p with
  | nil => simp [mulTerm]
  | cons t p ih =>
    rcases t with ⟨k, b⟩
    change MvPolynomial.monomial (exps (Vector.zipWith (· + ·) m k)) (a * b) +
      asPoly (mulTerm m a p) = _
    rw [ih, asPoly_cons, mul_add, MvPolynomial.monomial_mul_monomial, exps_add]

@[simp] theorem asPoly_mul (p q : MPoly n) : asPoly (mul p q) = asPoly p * asPoly q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
    rcases t with ⟨m, a⟩
    change asPoly (add (mulTerm m a q) (mul p q)) = _
    rw [asPoly_add, asPoly_mulTerm, ih, asPoly_cons, add_mul]

theorem asPoly_coeff (p : MPoly n) (m : Mono n) :
    (asPoly p).coeff (exps m) = coeff m p := by
  induction p with
  | nil => simp [coeff]
  | cons t p ih =>
    rcases t with ⟨k, a⟩
    by_cases h : k = m
    · subst h
      simp [asPoly_cons, coeff, ← ih, MvPolynomial.coeff_monomial]
    · have ne : exps k ≠ exps m := fun e => h (exps_injective e)
      have : (k == m) = false := by simpa using h
      simp [asPoly_cons, coeff, ← ih, MvPolynomial.coeff_monomial, ne, this]

theorem coeff_eq_zero_of_absent {m : Mono n} {p : MPoly n} (h : ∀ t ∈ p, t.1 ≠ m) :
    coeff m p = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨k, a⟩
    simp only [List.forall_mem_cons] at h
    have : (k == m) = false := by simpa using h.1
    simp [coeff, this, ih h.2]

theorem isZero_iff (p : MPoly n) : isZero p = true ↔ asPoly p = 0 := by
  simp only [isZero, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    ext f
    obtain ⟨m, rfl⟩ := exists_exps f
    rw [asPoly_coeff]
    change coeff m p = 0
    by_cases appears : ∃ t ∈ p, t.1 = m
    · obtain ⟨t, ht, hm⟩ := appears
      exact hm ▸ h t ht
    · exact coeff_eq_zero_of_absent fun t ht he => appears ⟨t, ht, he⟩
  · intro h t _
    rw [← asPoly_coeff, h]
    rfl

end MPoly

open MPoly

/-- Substitute field elements for the generators. -/
noncomputable abbrev specialize {F : Type*} [Field F] [CharZero F] (g : Fin n → F) :
    MvPolynomial (Fin n) ℚ →+* F :=
  MvPolynomial.eval₂Hom (Rat.castHom F) g

namespace Term

theorem equiv_iff_cross_mul (a b : Term n) :
    a.equiv b = true ↔
      asPoly (fraction a).1 * asPoly (fraction b).2 =
        asPoly (fraction b).1 * asPoly (fraction a).2 := by
  simp [equiv, isZero_iff, ← sub_eq_add_neg, sub_eq_zero]

/-- The numerator and denominator of a defined term denote its value. -/
theorem fraction_spec {F : Type*} [Field F] [CharZero F] (g : Fin n → F) (a : Term n)
    (ha : a.Defined g) :
    specialize g (asPoly (fraction a).1) = a.eval g * specialize g (asPoly (fraction a).2) ∧
      specialize g (asPoly (fraction a).2) ≠ 0 := by
  induction a with
  | const q => simp [fraction, specialize, eval]
  | gen i => simp [fraction, specialize, eval]
  | neg a ih =>
    obtain ⟨h, hn⟩ := ih ha
    simp only [fraction, asPoly_neg, map_neg, eval, h, neg_mul]
    exact ⟨trivial, hn⟩
  | add a b ia ib =>
    obtain ⟨h, hn⟩ := ia ha.1
    obtain ⟨j, jn⟩ := ib ha.2
    simp only [fraction, asPoly_add, asPoly_mul, map_mul, map_add, eval, h, j]
    exact ⟨by ring, mul_ne_zero hn jn⟩
  | sub a b ia ib =>
    obtain ⟨h, hn⟩ := ia ha.1
    obtain ⟨j, jn⟩ := ib ha.2
    simp only [fraction, asPoly_add, asPoly_mul, asPoly_neg, map_mul, map_add, map_neg, eval, h, j]
    exact ⟨by ring, mul_ne_zero hn jn⟩
  | mul a b ia ib =>
    obtain ⟨h, hn⟩ := ia ha.1
    obtain ⟨j, jn⟩ := ib ha.2
    simp only [fraction, asPoly_mul, map_mul, eval, h, j]
    exact ⟨by ring, mul_ne_zero hn jn⟩
  | div a b ia ib =>
    obtain ⟨h, hn⟩ := ia ha.1
    obtain ⟨j, jn⟩ := ib ha.2.1
    have hb := ha.2.2
    simp only [fraction, asPoly_mul, map_mul, eval, h, j]
    exact ⟨by field_simp [hb], mul_ne_zero hn (mul_ne_zero hb jn)⟩

/-- A successful comparison is valid wherever both terms are defined. -/
theorem eval_eq_of_equiv {F : Type*} [Field F] [CharZero F] (g : Fin n → F) {a b : Term n}
    (h : a.equiv b = true) (ha : a.Defined g) (hb : b.Defined g) : a.eval g = b.eval g := by
  obtain ⟨pa, qa⟩ := fraction_spec g a ha
  obtain ⟨pb, qb⟩ := fraction_spec g b hb
  have he := congrArg (specialize g) ((equiv_iff_cross_mul a b).mp h)
  simp only [map_mul, pa, pb] at he
  apply mul_right_cancel₀ (mul_ne_zero qa qb)
  calc
    _ = _ := (mul_assoc ..).symm
    _ = _ := he
    _ = _ := by ring

end Term

variable (k : Type) [Field k] [CharZero k]

/-- The generators of a tower field are algebraically independent over the rationals. -/
theorem specialize_injective : ∀ n : ℕ, Function.Injective (specialize (gens k n))
  | 0 => by
    let e := MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)
    have he : specialize (gens k 0) = (Rat.castHom k).comp e.toRingHom := by
      apply MvPolynomial.ringHom_ext'
      · exact Subsingleton.elim ..
      · exact fun i => i.elim0
    rw [he]
    exact (Rat.castHom k).injective.comp e.injective
  | n + 1 => by
    have ih := specialize_injective n
    let v := specialize (gens k n)
    let rot := MvPolynomial.renameEquiv ℚ (finRotate (n + 1))
    let e := MvPolynomial.finSuccEquiv ℚ n
    let P := Polynomial.mapRingHom v
    let ι := algebraMap (Polynomial (K k n)) (RatFunc (K k n))
    have he : specialize (gens k (n + 1)) =
        ι.comp (P.comp (e.toRingHom.comp rot.toRingHom)) := by
      apply MvPolynomial.ringHom_ext' (Subsingleton.elim ..)
      simp only [specialize, MvPolynomial.eval₂Hom_X']
      change ∀ i, gens k (n + 1) i = ι (Polynomial.map v (e (rot (MvPolynomial.X i))))
      apply Fin.lastCases
      · simp only [rot, e, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, finRotate_last,
          MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, ι, RatFunc.algebraMap_X]
        simp [gens]
      · intro j
        have hrot : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
        simp only [rot, e, ι, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hrot,
          MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, RatFunc.algebraMap_C]
        simp [v, specialize, gens]
    rw [he]
    exact (RatFunc.algebraMap_injective _).comp ((Polynomial.map_injective v ih).comp
      (e.injective.comp rot.injective))

variable {k}

namespace Term

/-- For terms defined in the field of a tower, the comparison decides equality there. -/
theorem equiv_iff_value_eq {a b : Term n} (ha : InDomain k a) (hb : InDomain k b) :
    a.equiv b = true ↔ value k a = value k b := by
  refine ⟨fun h => eval_eq_of_equiv _ h ha hb, fun h => ?_⟩
  apply (equiv_iff_cross_mul a b).mpr
  apply specialize_injective k n
  obtain ⟨pa, _⟩ := fraction_spec _ a ha
  obtain ⟨pb, _⟩ := fraction_spec _ b hb
  change a.eval _ = b.eval _ at h
  simp only [map_mul, pa, pb, h]
  ring

theorem value_const (q : ℚ) : value k (.const q : Term n) = (q : K k n) := rfl

/-- For a term defined in the field of a tower, the zero test decides whether it vanishes. -/
theorem isZero_iff {a : Term n} (ha : InDomain k a) : a.isZero = true ↔ value k a = 0 := by
  rw [isZero, equiv_iff_value_eq ha (show InDomain k (.const 0 : Term n) from trivial),
    value_const, Rat.cast_zero]

/-- The test for vanishing denominators decides definedness, over every constant field. -/
theorem defined_iff (e : Term n) : e.defined = true ↔ InDomain k e := by
  induction e with
  | const | gen => simp [defined, InDomain, Defined]
  | neg a ih => exact ih
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    simpa only [defined, Bool.and_eq_true, InDomain, Defined] using and_congr ia ib
  | div a b ia ib =>
    simp only [defined, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ia, ib]
    change (_ ∧ _) ∧ _ ↔ _ ∧ _ ∧ value k b ≠ 0
    exact ⟨fun ⟨⟨ha, hb⟩, h⟩ => ⟨ha, hb, fun hv => h ((isZero_iff hb).mpr hv)⟩,
      fun ⟨ha, hb, h⟩ => ⟨⟨ha, hb⟩, fun he => h ((isZero_iff hb).mp he)⟩⟩

/-- The rational number found is the value of the term, and one is found whenever the value
is a rational number. -/
theorem scalar?_eq_some_iff {e : Term n} (he : InDomain k e) (c : ℚ) :
    e.scalar? = some c ↔ value k e = (c : K k n) := by
  obtain ⟨p, hp⟩ : ∃ p, p = (fraction e).1 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = (fraction e).2 := ⟨_, rfl⟩
  have dne : asPoly d ≠ 0 := by
    intro h
    have hn := (fraction_spec (gens k n) e he).2
    exact hn (by rw [← hd, h, map_zero])
  have someTerm : ∃ m, d.find? (fun t => MPoly.coeff t.1 d != 0) = some m := by
    cases h : d.find? (fun t => MPoly.coeff t.1 d != 0) with
    | some m => exact ⟨m, rfl⟩
    | none =>
      exfalso
      apply dne
      apply (MPoly.isZero_iff _).mp
      have := List.find?_eq_none.mp h
      simpa [MPoly.isZero, List.all_eq_true] using this
  obtain ⟨m, hm⟩ := someTerm
  have hn : MPoly.coeff m.1 d ≠ 0 := by
    have := List.find?_some hm
    simpa using this
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = MPoly.coeff m.1 p / MPoly.coeff m.1 d := ⟨_, rfl⟩
  have run : e.scalar? = (if e.equiv (.const c0) then some c0 else none) := by
    rw [scalar?, ← hd, hm, ← hp]
    subst hc0
    rfl
  rw [run]
  constructor
  · split
    · rename_i eqn
      intro h
      have hk : c0 = c := Option.some.inj h
      rw [← hk]
      exact (equiv_iff_value_eq he (b := .const _) trivial).mp eqn
    · simp
  · intro hv
    have eqn := (equiv_iff_value_eq he (b := .const c) trivial).mpr hv
    have hpd : asPoly p = MvPolynomial.C c * asPoly d := by
      have := (equiv_iff_cross_mul ..).mp eqn
      simpa [fraction, ← hp, ← hd] using this
    have hc := congrArg (fun v : MvPolynomial (Fin n) ℚ => v.coeff (exps m.1)) hpd
    simp only [MvPolynomial.coeff_C_mul, asPoly_coeff] at hc
    have hk : c0 = c := by
      rw [hc0]
      exact (div_eq_iff hn).mpr hc
    simp [hk, eqn]

end Term

end SympyProofs.Calculus.Risch
