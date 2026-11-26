module

public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Raw
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.FastInstance
import Mathlib.Tactic.Ring

/-! The polynomials `Poly R`: lists of coefficients, two lists being equal when they have the
same coefficient at every degree. `Poly R` is the quotient of the lists `Poly.Raw R` by that
relation, as `Multiset` is a quotient of `List`. A value is still the list at run time, and an
operation is the operation on lists of `Poly/Raw.lean`.

The file has three parts.

* `Poly.Raw`: the relation `Poly.Raw.Rel`, and for each operation on lists the theorem that it
  respects the relation (`Poly.Raw.add_congr`, …). Most of them come from
  `Poly.Raw.toPolynomial`, Mathlib's polynomial with the coefficients of the list: two lists
  are related exactly when they have the same Mathlib polynomial, and each operation on lists
  is the operation of Mathlib there.
* `Poly R`: the quotient, the operations lifted to it, and what is read off a polynomial:
  `coeffs` (the list without vanishing coefficients of highest degree), `coeff`, `natDegree`,
  `leadingCoeff`. Equality is decided by comparing the lists of coefficients.
* The laws. `Poly.toPolynomial` is injective and surjective and respects every operation, so
  the laws of a commutative ring are transferred along it: none is proved by hand. It is the
  ring equivalence `Poly.equiv : Poly R ≃+* R[X]`, and the simp lemmas `equiv_C`, `equiv_X`,
  `coeff_equiv`, `natDegree_equiv`, `leadingCoeff_equiv`, `equiv_derivative`, `equiv_map`,
  `eval_equiv`, `equiv_algebraMap`, `equiv_ofList` say what it does to each operation.
  Polynomials over an algebra are an algebra, polynomials over a domain are a domain, and
  they have characteristic zero when the coefficients do. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open scoped Polynomial

universe u

namespace Poly.Raw

variable {R : Type}

/-! ### Lists with the same coefficients -/

section Rel

variable [Zero R]

@[simp] theorem coeff_nil (n : ℕ) : coeff ([] : Raw R) n = 0 := rfl

@[simp] theorem coeff_cons_zero (c : R) (cs : Raw R) : coeff (c :: cs) 0 = c := rfl

@[simp] theorem coeff_cons_succ (c : R) (cs : Raw R) (n : ℕ) :
    coeff (c :: cs) (n + 1) = coeff cs n := rfl

/-- The coefficients beyond the end of the list vanish. -/
theorem coeff_eq_zero_of_length_le {p : Raw R} {n : ℕ} (h : p.length ≤ n) : coeff p n = 0 := by
  rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- Two lists are the same polynomial: they have the same coefficient at every degree. -/
def Rel (p q : Raw R) : Prop := ∀ n, coeff p n = coeff q n

theorem Rel.refl (p : Raw R) : Rel p p := fun _ => rfl

theorem Rel.symm {p q : Raw R} (h : Rel p q) : Rel q p := fun n => (h n).symm

theorem Rel.trans {p q r : Raw R} (h₁ : Rel p q) (h₂ : Rel q r) : Rel p r :=
  fun n => (h₁ n).trans (h₂ n)

variable (R) in
/-- The lists of coefficients, up to vanishing coefficients of highest degree. -/
def setoid : Setoid (Raw R) := ⟨Rel, ⟨Rel.refl, Rel.symm, Rel.trans⟩⟩

/-- The coefficient of a given degree respects the relation. -/
theorem coeff_congr {p q : Raw R} (h : Rel p q) (n : ℕ) : coeff p n = coeff q n := h n

/-- The coefficients of the image of a list by a function that fixes zero. -/
theorem coeff_listMap {S : Type} [Zero S] (f : R → S) (hf : f 0 = 0) :
    ∀ (p : Raw R) (n : ℕ), coeff (List.map f p) n = f (coeff p n)
  | [], _ => hf.symm
  | _ :: _, 0 => rfl
  | _ :: cs, n + 1 => coeff_listMap f hf cs n

variable [DecidableEq R]

theorem trim_cons (c : R) (cs : Raw R) :
    trim (c :: cs) = if trim cs = [] then (if c = 0 then [] else [c]) else c :: trim cs := by
  simp [trim, List.isEmpty_iff]

/-- Trimming keeps every coefficient. -/
theorem coeff_trim : ∀ (p : Raw R) (n : ℕ), coeff (trim p) n = coeff p n
  | [], _ => rfl
  | c :: cs, n => by
    have ih := coeff_trim cs
    rw [trim_cons]
    split_ifs with h hc
    · rw [h] at ih
      cases n with
      | zero => simp [hc]
      | succ n => simpa using ih n
    · rw [h] at ih
      cases n with
      | zero => simp
      | succ n => simpa using ih n
    · cases n with
      | zero => simp
      | succ n => simpa using ih n

/-- A list is the same polynomial as its trimmed list. -/
theorem rel_trim (p : Raw R) : Rel (trim p) p := coeff_trim p

/-- A list all of whose coefficients vanish trims to the empty list. -/
theorem trim_eq_nil : ∀ {p : Raw R}, (∀ n, coeff p n = 0) → trim p = []
  | [], _ => rfl
  | c :: cs, h => by
    have ih : trim cs = [] := trim_eq_nil fun n => h (n + 1)
    have hc : c = 0 := h 0
    simp [trim_cons, ih, hc]

/-- Trimming respects the relation, and more: two lists that are the same polynomial trim to
the same list. -/
theorem trim_congr : ∀ {p q : Raw R}, Rel p q → trim p = trim q
  | [], _, h => (trim_eq_nil fun n => (h n).symm).symm
  | _ :: _, [], h => trim_eq_nil h
  | c :: cs, d :: ds, h => by
    have ih : trim cs = trim ds := trim_congr fun n => h (n + 1)
    have hc : c = d := h 0
    rw [trim_cons, trim_cons, ih, hc]

/-- Two lists are the same polynomial exactly when they trim to the same list. -/
theorem rel_iff_trim_eq {p q : Raw R} : Rel p q ↔ trim p = trim q :=
  ⟨trim_congr, fun h => (rel_trim p).symm.trans (h ▸ rel_trim q)⟩

/-- Trimming a trimmed list does nothing. -/
@[simp] theorem trim_trim (p : Raw R) : trim (trim p) = trim p := trim_congr (rel_trim p)

/-- The last coefficient of a trimmed list is not zero. -/
theorem getLast?_trim : ∀ p : Raw R, (trim p).getLast? ≠ some 0
  | [] => by simp [trim]
  | c :: cs => by
    have ih := getLast?_trim cs
    rw [trim_cons]
    split_ifs with h hc
    · simp
    · simpa using hc
    · obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil h
      rw [hd] at ih ⊢
      simpa [List.getLast?_cons_cons] using ih

/-- Trimming a list whose last element is not zero does nothing. -/
theorem trim_eq_self : ∀ {p : Raw R}, p.getLast? ≠ some 0 → trim p = p
  | [], _ => rfl
  | [c], h => by
    have hc : c ≠ 0 := by simpa using h
    simp [trim, hc]
  | c :: d :: l, h => by
    have ih : trim (d :: l) = d :: l :=
      trim_eq_self (by simpa [List.getLast?_cons_cons] using h)
    rw [trim_cons, ih]
    simp

/-- The degree respects the relation. -/
theorem natDegree_congr {p q : Raw R} (h : Rel p q) : natDegree p = natDegree q := by
  rw [natDegree, natDegree, trim_congr h]

/-- The leading coefficient respects the relation. -/
theorem leadingCoeff_congr {p q : Raw R} (h : Rel p q) : leadingCoeff p = leadingCoeff q := by
  rw [leadingCoeff, leadingCoeff, trim_congr h]

/-- The leading coefficient is the coefficient of the degree. -/
theorem coeff_natDegree (p : Raw R) : coeff p (natDegree p) = leadingCoeff p := by
  rw [← coeff_trim, natDegree, leadingCoeff, coeff]
  generalize trim p = t
  cases t using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a => simp

/-- The leading coefficient of a list that does not trim to the empty list is not zero. -/
theorem leadingCoeff_ne_zero {p : Raw R} (h : trim p ≠ []) : leadingCoeff p ≠ 0 := by
  have hl := getLast?_trim p
  rw [leadingCoeff]
  generalize trim p = t at h hl
  cases t using List.reverseRecOn with
  | nil => exact absurd rfl h
  | append_singleton l a => simpa using hl

/-- The coefficients above the degree vanish. -/
theorem coeff_eq_zero_of_natDegree_lt {p : Raw R} {n : ℕ} (h : natDegree p < n) :
    coeff p n = 0 := by
  rw [← coeff_trim]
  exact coeff_eq_zero_of_length_le (by rw [natDegree] at h; omega)

/-- The image by any function depends only on the polynomial. -/
theorem map_congr {S : Type} [Zero S] [DecidableEq S] (f : R → S) {p q : Raw R}
    (h : Rel p q) : map f p = map f q := by
  rw [map, map, trim_congr h]

/-- The coefficients of the image by a function that fixes zero. -/
theorem coeff_map {S : Type} [Zero S] [DecidableEq S] (f : R → S) (hf : f 0 = 0) (p : Raw R)
    (n : ℕ) : coeff (map f p) n = f (coeff p n) := by
  rw [map, coeff_trim, coeff_listMap f hf, coeff_trim]

end Rel

/-! ### The polynomial of a list -/

section ToPolynomial

variable [CommRing R]

/-- Mathlib's polynomial with the given coefficients, from degree zero. -/
noncomputable def toPolynomial : Raw R → R[X]
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * toPolynomial cs

@[simp] theorem toPolynomial_nil : toPolynomial ([] : Raw R) = 0 := rfl

@[simp] theorem toPolynomial_cons (c : R) (cs : Raw R) :
    toPolynomial (c :: cs) = Polynomial.C c + Polynomial.X * toPolynomial cs := rfl

/-- The coefficients of the polynomial of a list are the elements of the list. -/
@[simp] theorem coeff_toPolynomial : ∀ (p : Raw R) (n : ℕ),
    (toPolynomial p).coeff n = coeff p n
  | [], n => by simp
  | c :: cs, 0 => by simp
  | c :: cs, n + 1 => by simp [coeff_toPolynomial cs n]

/-- Two lists are the same polynomial exactly when they have the same Mathlib polynomial. -/
theorem toPolynomial_inj {p q : Raw R} : toPolynomial p = toPolynomial q ↔ Rel p q :=
  ⟨fun h n => by rw [← coeff_toPolynomial, ← coeff_toPolynomial, h], fun h => by
    ext n
    rw [coeff_toPolynomial, coeff_toPolynomial, h n]⟩

/-- The polynomial of a list respects the relation. -/
theorem toPolynomial_congr {p q : Raw R} (h : Rel p q) : toPolynomial p = toPolynomial q :=
  toPolynomial_inj.mpr h

theorem toPolynomial_addAux : ∀ p q : Raw R,
    toPolynomial (addAux p q) = toPolynomial p + toPolynomial q
  | [], q => by simp [addAux]
  | a :: p, [] => by simp [addAux]
  | a :: p, b :: q => by
    simp only [addAux, toPolynomial_cons, toPolynomial_addAux p q, map_add]
    ring

theorem toPolynomial_map_neg (p : Raw R) :
    toPolynomial (List.map (- ·) p) = -toPolynomial p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.map_cons, toPolynomial_cons, ih, map_neg]
    ring

theorem toPolynomial_subAux : ∀ p q : Raw R,
    toPolynomial (subAux p q) = toPolynomial p - toPolynomial q
  | [], q => by simp [subAux, toPolynomial_map_neg]
  | a :: p, [] => by simp [subAux]
  | a :: p, b :: q => by
    simp only [subAux, toPolynomial_cons, toPolynomial_subAux p q, map_sub]
    ring

theorem toPolynomial_map_mul (a : R) (q : Raw R) :
    toPolynomial (List.map (a * ·) q) = Polynomial.C a * toPolynomial q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, toPolynomial_cons, ih, map_mul]
    ring

theorem toPolynomial_map_smul {A : Type u} [SMulZeroClass A R] (a : A) (p : Raw R) :
    toPolynomial (List.map (a • ·) p) = a • toPolynomial p := by
  ext n
  rw [AddMonoidAlgebra.coeff_smul_apply, coeff_toPolynomial, coeff_toPolynomial,
    coeff_listMap _ (smul_zero a)]

theorem toPolynomial_derivativeAux : ∀ (k : R) (p : Raw R),
    toPolynomial (derivativeAux k p) =
      Polynomial.C k * toPolynomial p + Polynomial.X * (toPolynomial p).derivative
  | k, [] => by simp [derivativeAux]
  | k, c :: cs => by
    simp only [derivativeAux, toPolynomial_cons, toPolynomial_derivativeAux (k + 1) cs, map_mul,
      map_add, map_one, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X]
    ring

/-- The value by Horner's rule is the value of the polynomial of the list. -/
theorem eval_toPolynomial (x : R) (p : Raw R) : (toPolynomial p).eval x = eval x p := by
  induction p with
  | nil => simp [eval]
  | cons c cs ih => simp [eval, ih]

/-- The value at a point respects the relation. -/
theorem eval_congr (x : R) {p q : Raw R} (h : Rel p q) : eval x p = eval x q := by
  rw [← eval_toPolynomial, ← eval_toPolynomial, toPolynomial_congr h]

theorem toPolynomial_listMap {S : Type} [CommRing S] (f : R →+* S) (p : Raw R) :
    toPolynomial (List.map f p) = (toPolynomial p).map f := by
  induction p with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem toPolynomial_replicate_append (n : ℕ) (p : Raw R) :
    toPolynomial (List.replicate n 0 ++ p) = Polynomial.X ^ n * toPolynomial p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, toPolynomial_cons, ih, map_zero]
    ring

variable [DecidableEq R]

/-- Trimming a list does not change its polynomial. -/
@[simp] theorem toPolynomial_trim (p : Raw R) : toPolynomial (trim p) = toPolynomial p :=
  toPolynomial_congr (rel_trim p)

theorem toPolynomial_C (a : R) : toPolynomial (C a) = Polynomial.C a := by
  rw [C]
  split
  · next h => simp [show a = 0 by simpa using h]
  · simp

theorem toPolynomial_X : toPolynomial (X : Raw R) = Polynomial.X := by
  simp [X]

theorem toPolynomial_monomial (n : ℕ) (a : R) :
    toPolynomial (monomial n a) = Polynomial.monomial n a := by
  rw [monomial]
  split
  · next h => simp [show a = 0 by simpa using h]
  · rw [toPolynomial_replicate_append, ← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
    simp

theorem toPolynomial_add (p q : Raw R) :
    toPolynomial (add p q) = toPolynomial p + toPolynomial q :=
  (toPolynomial_trim _).trans (toPolynomial_addAux p q)

theorem toPolynomial_neg (p : Raw R) : toPolynomial (neg p) = -toPolynomial p :=
  (toPolynomial_trim _).trans (toPolynomial_map_neg p)

theorem toPolynomial_sub (p q : Raw R) :
    toPolynomial (sub p q) = toPolynomial p - toPolynomial q :=
  (toPolynomial_trim _).trans (toPolynomial_subAux p q)

theorem toPolynomial_smul {A : Type u} [SMulZeroClass A R] (a : A) (p : Raw R) :
    toPolynomial (smul a p) = a • toPolynomial p :=
  (toPolynomial_trim _).trans (toPolynomial_map_smul a p)

theorem toPolynomial_mulAux (b : R) (q : Raw R) : ∀ p : Raw R,
    toPolynomial (mulAux b q p) = toPolynomial p * toPolynomial (b :: q)
  | [] => by simp [mulAux]
  | a :: p => by
    have ih := toPolynomial_mulAux b q p
    rw [mulAux]
    split
    · next h =>
      simp only [toPolynomial_cons, ih, show a = 0 by simpa using h, map_zero]
      ring
    · simp only [toPolynomial_cons, toPolynomial_addAux, toPolynomial_map_mul, ih, map_mul]
      ring

theorem toPolynomial_mul (p q : Raw R) :
    toPolynomial (mul p q) = toPolynomial p * toPolynomial q := by
  cases q with
  | nil => simp [mul]
  | cons b q => rw [mul, toPolynomial_trim, toPolynomial_mulAux]

theorem toPolynomial_pow (p : Raw R) (n : ℕ) :
    toPolynomial (pow p n) = toPolynomial p ^ n := by
  induction n with
  | zero => simp [pow, toPolynomial_C]
  | succ n ih => rw [pow, toPolynomial_mul, ih, pow_succ]

theorem toPolynomial_derivative (p : Raw R) :
    toPolynomial (derivative p) = (toPolynomial p).derivative := by
  cases p with
  | nil => simp [derivative]
  | cons c cs =>
    simp only [derivative, toPolynomial_trim, toPolynomial_derivativeAux, toPolynomial_cons,
      map_one, Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X]
    ring

theorem toPolynomial_map {S : Type} [CommRing S] [DecidableEq S] (f : R →+* S) (p : Raw R) :
    toPolynomial (map f p) = (toPolynomial p).map f := by
  rw [map, toPolynomial_trim, toPolynomial_listMap, toPolynomial_trim]

/-- The sum respects the relation. -/
theorem add_congr {p p' q q' : Raw R} (hp : Rel p p') (hq : Rel q q') :
    Rel (add p q) (add p' q') := by
  rw [← toPolynomial_inj] at hp hq ⊢
  rw [toPolynomial_add, toPolynomial_add, hp, hq]

/-- The opposite respects the relation. -/
theorem neg_congr {p p' : Raw R} (hp : Rel p p') : Rel (neg p) (neg p') := by
  rw [← toPolynomial_inj] at hp ⊢
  rw [toPolynomial_neg, toPolynomial_neg, hp]

/-- The difference respects the relation. -/
theorem sub_congr {p p' q q' : Raw R} (hp : Rel p p') (hq : Rel q q') :
    Rel (sub p q) (sub p' q') := by
  rw [← toPolynomial_inj] at hp hq ⊢
  rw [toPolynomial_sub, toPolynomial_sub, hp, hq]

/-- The product respects the relation. -/
theorem mul_congr {p p' q q' : Raw R} (hp : Rel p p') (hq : Rel q q') :
    Rel (mul p q) (mul p' q') := by
  rw [← toPolynomial_inj] at hp hq ⊢
  rw [toPolynomial_mul, toPolynomial_mul, hp, hq]

/-- The action of a scalar respects the relation. -/
theorem smul_congr {A : Type u} [SMulZeroClass A R] (a : A) {p p' : Raw R} (hp : Rel p p') :
    Rel (smul a p) (smul a p') := by
  rw [← toPolynomial_inj] at hp ⊢
  rw [toPolynomial_smul, toPolynomial_smul, hp]

/-- The power respects the relation. -/
theorem pow_congr {p p' : Raw R} (hp : Rel p p') (n : ℕ) : Rel (pow p n) (pow p' n) := by
  rw [← toPolynomial_inj] at hp ⊢
  rw [toPolynomial_pow, toPolynomial_pow, hp]

/-- The formal derivative respects the relation. -/
theorem derivative_congr {p p' : Raw R} (hp : Rel p p') :
    Rel (derivative p) (derivative p') := by
  rw [← toPolynomial_inj] at hp ⊢
  rw [toPolynomial_derivative, toPolynomial_derivative, hp]

end ToPolynomial

end Poly.Raw

/-! ### The quotient -/

/-- The polynomials in one variable over `R`: the lists of coefficients, two lists being
equal when they have the same coefficient at every degree. -/
def Poly (R : Type) [Zero R] := Quotient (Poly.Raw.setoid R)

namespace Poly

variable {R : Type}

section Zero

variable [Zero R]

/-- The polynomial with the given coefficients, from degree zero. -/
def ofList (l : List R) : Poly R := Quotient.mk (Raw.setoid R) l

/-- Two lists give the same polynomial exactly when they have the same coefficients. -/
theorem ofList_eq_ofList {p q : List R} : ofList p = ofList q ↔ Raw.Rel p q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every polynomial is the polynomial of a list. -/
@[elab_as_elim] theorem induction_on {motive : Poly R → Prop} (p : Poly R)
    (h : ∀ l : List R, motive (ofList l)) : motive p :=
  Quotient.inductionOn p h

/-- Every two polynomials are the polynomials of two lists. -/
@[elab_as_elim] theorem induction_on₂ {motive : Poly R → Poly R → Prop} (p q : Poly R)
    (h : ∀ l m : List R, motive (ofList l) (ofList m)) : motive p q :=
  Quotient.inductionOn₂ p q h

/-- The zero polynomial has no coefficients. -/
instance : Zero (Poly R) := ⟨ofList []⟩

/-- The zero polynomial, as a default value. -/
instance : Inhabited (Poly R) := ⟨0⟩

@[simp] theorem ofList_nil : ofList ([] : List R) = 0 := rfl

/-- The coefficient of degree `n`. -/
def coeff (p : Poly R) (n : ℕ) : R :=
  Quotient.lift (s := Raw.setoid R) (fun l => Raw.coeff l n) (fun _ _ h => Raw.coeff_congr h n) p

/-- The coefficients of `ofList l` are the elements of `l`. -/
@[simp] theorem coeff_ofList (l : List R) (n : ℕ) : (ofList l).coeff n = l.getD n 0 := rfl

@[simp] theorem coeff_zero (n : ℕ) : (0 : Poly R).coeff n = 0 := rfl

/-- Two polynomials with the same coefficients are equal. -/
@[ext] theorem ext {p q : Poly R} (h : ∀ n, p.coeff n = q.coeff n) : p = q := by
  induction p, q using induction_on₂ with
  | h l m => exact ofList_eq_ofList.mpr h

variable [DecidableEq R]

/-- The list of coefficients, from degree zero, without vanishing coefficients of highest
degree. The zero polynomial has the empty list. -/
def coeffs (p : Poly R) : List R :=
  Quotient.lift (s := Raw.setoid R) Raw.trim (fun _ _ h => Raw.trim_congr h) p

/-- The degree, and zero for the zero polynomial. -/
def natDegree (p : Poly R) : ℕ :=
  Quotient.lift (s := Raw.setoid R) Raw.natDegree (fun _ _ h => Raw.natDegree_congr h) p

/-- The coefficient of highest degree, and zero for the zero polynomial. -/
def leadingCoeff (p : Poly R) : R :=
  Quotient.lift (s := Raw.setoid R) Raw.leadingCoeff
    (fun _ _ h => Raw.leadingCoeff_congr h) p

/-- The constant polynomial. -/
def C (a : R) : Poly R := ofList (Raw.C a)

/-- The variable. -/
def X [One R] : Poly R := ofList Raw.X

/-- The polynomial `a Xⁿ`. -/
def monomial (n : ℕ) (a : R) : Poly R := ofList (Raw.monomial n a)

/-- Apply a function to every coefficient of the list `coeffs`. For a function that fixes zero
these are the coefficients of the result (`coeff_map`); any function will do. -/
def map {S : Type} [Zero S] [DecidableEq S] (f : R → S) (p : Poly R) : Poly S :=
  Quotient.lift (s := Raw.setoid R) (fun l => ofList (Raw.map f l))
    (fun _ _ h => congrArg ofList (Raw.map_congr f h)) p

@[simp] theorem coeffs_ofList (l : List R) : (ofList l).coeffs = Raw.trim l := rfl

@[simp] theorem natDegree_ofList (l : List R) : (ofList l).natDegree = Raw.natDegree l := rfl

@[simp] theorem leadingCoeff_ofList (l : List R) :
    (ofList l).leadingCoeff = Raw.leadingCoeff l := rfl

theorem map_ofList {S : Type} [Zero S] [DecidableEq S] (f : R → S) (l : List R) :
    (ofList l).map f = ofList (Raw.map f l) := rfl

/-- Trimming a list does not change its polynomial. -/
@[simp] theorem ofList_trim (l : List R) : ofList (Raw.trim l) = ofList l :=
  ofList_eq_ofList.mpr (Raw.rel_trim l)

/-- A polynomial is the polynomial of its list of coefficients. -/
@[simp] theorem ofList_coeffs (p : Poly R) : ofList p.coeffs = p := by
  induction p using induction_on with
  | h l => exact ofList_eq_ofList.mpr (Raw.rel_trim l)

/-- The list of coefficients of a polynomial is already trimmed. -/
@[simp] theorem trim_coeffs (p : Poly R) : Raw.trim p.coeffs = p.coeffs := by
  induction p using induction_on with
  | h l => exact Raw.trim_trim l

/-- The last coefficient of the list of coefficients is not zero. -/
theorem getLast?_coeffs (p : Poly R) : p.coeffs.getLast? ≠ some 0 := by
  induction p using induction_on with
  | h l => exact Raw.getLast?_trim l

/-- Two polynomials are equal exactly when they have the same list of coefficients. -/
theorem coeffs_inj {p q : Poly R} : p.coeffs = q.coeffs ↔ p = q :=
  ⟨fun h => by rw [← ofList_coeffs p, ← ofList_coeffs q, h], fun h => h ▸ rfl⟩

@[simp] theorem coeffs_zero : (0 : Poly R).coeffs = [] := rfl

/-- The polynomial without coefficients is zero. -/
theorem coeffs_eq_nil {p : Poly R} : p.coeffs = [] ↔ p = 0 := coeffs_inj (q := 0)

/-- The coefficients are the elements of the list of coefficients. -/
theorem coeff_eq_getD_coeffs (p : Poly R) (n : ℕ) : p.coeff n = p.coeffs.getD n 0 := by
  induction p using induction_on with
  | h l => exact (Raw.coeff_trim l n).symm

/-- The degree is one less than the number of coefficients. -/
theorem natDegree_eq (p : Poly R) : p.natDegree = p.coeffs.length - 1 := by
  induction p using induction_on with
  | h l => rfl

/-- The leading coefficient is the last element of the list of coefficients. -/
theorem leadingCoeff_eq (p : Poly R) : p.leadingCoeff = p.coeffs.getLastD 0 := by
  induction p using induction_on with
  | h l => rfl

@[simp] theorem natDegree_zero : (0 : Poly R).natDegree = 0 := rfl

@[simp] theorem leadingCoeff_zero : (0 : Poly R).leadingCoeff = 0 := rfl

/-- The leading coefficient is the coefficient of the degree. -/
theorem coeff_natDegree (p : Poly R) : p.coeff p.natDegree = p.leadingCoeff := by
  induction p using induction_on with
  | h l => exact Raw.coeff_natDegree l

/-- The leading coefficient of a polynomial that is not zero is not zero. -/
theorem leadingCoeff_ne_zero {p : Poly R} (h : p ≠ 0) : p.leadingCoeff ≠ 0 := by
  induction p using induction_on with
  | h l => exact Raw.leadingCoeff_ne_zero fun hl => h (coeffs_eq_nil.mp hl)

/-- Only the zero polynomial has leading coefficient zero. -/
@[simp] theorem leadingCoeff_eq_zero {p : Poly R} : p.leadingCoeff = 0 ↔ p = 0 :=
  ⟨fun h => by_contra fun hp => leadingCoeff_ne_zero hp h, fun h => h ▸ rfl⟩

/-- The coefficients above the degree vanish. -/
theorem coeff_eq_zero_of_natDegree_lt {p : Poly R} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  induction p using induction_on with
  | h l => exact Raw.coeff_eq_zero_of_natDegree_lt h

/-- The list of coefficients of the image by any function. -/
theorem coeffs_map {S : Type} [Zero S] [DecidableEq S] (f : R → S) (p : Poly R) :
    (p.map f).coeffs = Raw.trim (p.coeffs.map f) := by
  induction p using induction_on with
  | h l => exact Raw.trim_trim _

/-- The coefficients of the image by a function that fixes zero. -/
theorem coeff_map {S : Type} [Zero S] [DecidableEq S] (f : R → S) (hf : f 0 = 0) (p : Poly R)
    (n : ℕ) : (p.map f).coeff n = f (p.coeff n) := by
  induction p using induction_on with
  | h l => exact Raw.coeff_map f hf l n

/-- Equality of polynomials is decided by comparing the lists of coefficients. -/
instance : DecidableEq (Poly R) := fun p q => decidable_of_iff (p.coeffs = q.coeffs) coeffs_inj

/-- A polynomial is shown as the list of its coefficients. -/
instance [Repr R] : Repr (Poly R) :=
  ⟨fun p n => Repr.addAppParen ("Poly.ofList " ++ reprArg p.coeffs) n⟩

end Zero

/-! ### The value at a point, and Mathlib's polynomial

Neither compares coefficients, so they are defined without decidable equality. -/

section Ring

variable [CommRing R]

/-- The value of the polynomial at `x`. -/
def eval (x : R) (p : Poly R) : R :=
  Quotient.lift (s := Raw.setoid R) (Raw.eval x) (fun _ _ h => Raw.eval_congr x h) p

theorem eval_ofList (x : R) (l : List R) : (ofList l).eval x = Raw.eval x l := rfl

/-- Mathlib's polynomial with the same coefficients. -/
noncomputable def toPolynomial (p : Poly R) : R[X] :=
  Quotient.lift (s := Raw.setoid R) Raw.toPolynomial (fun _ _ h => Raw.toPolynomial_congr h) p

theorem toPolynomial_ofList (l : List R) : (ofList l).toPolynomial = Raw.toPolynomial l := rfl

/-- The coefficients of Mathlib's polynomial are the coefficients. -/
theorem coeff_toPolynomial (p : Poly R) (n : ℕ) : p.toPolynomial.coeff n = p.coeff n := by
  induction p using induction_on with
  | h l => exact Raw.coeff_toPolynomial l n

/-- Polynomials with the same Mathlib polynomial are equal. -/
theorem toPolynomial_injective : Function.Injective (toPolynomial : Poly R → R[X]) :=
  fun p q h => ext fun n => by rw [← coeff_toPolynomial, ← coeff_toPolynomial, h]

theorem toPolynomial_zero : (0 : Poly R).toPolynomial = 0 := rfl

/-! ### The operations of a ring

Each is the operation on lists of `Poly/Raw.lean`, lifted by the theorem that it respects the
relation. The instances are given by named functions (`Poly.add`, …), so that an instance
never has to be unfolded down to the quotient. -/

variable [DecidableEq R]

/-- The constant polynomial one. -/
instance : One (Poly R) := ⟨C 1⟩

/-- The sum. -/
protected def add : Poly R → Poly R → Poly R :=
  Quotient.map₂ Raw.add fun _ _ hp _ _ hq => Raw.add_congr hp hq

/-- The opposite. -/
protected def neg : Poly R → Poly R := Quotient.map Raw.neg fun _ _ hp => Raw.neg_congr hp

/-- The difference. -/
protected def sub : Poly R → Poly R → Poly R :=
  Quotient.map₂ Raw.sub fun _ _ hp _ _ hq => Raw.sub_congr hp hq

/-- The product. -/
protected def mul : Poly R → Poly R → Poly R :=
  Quotient.map₂ Raw.mul fun _ _ hp _ _ hq => Raw.mul_congr hp hq

/-- The action of a scalar on every coefficient. -/
protected def smul {A : Type u} [SMulZeroClass A R] (a : A) : Poly R → Poly R :=
  Quotient.map (Raw.smul a) fun _ _ hp => Raw.smul_congr a hp

/-- The power, by repeated product. -/
protected def pow (p : Poly R) (n : ℕ) : Poly R :=
  Quotient.map (sa := Raw.setoid R) (Raw.pow · n) (fun _ _ hp => Raw.pow_congr hp n) p

/-- The sum of polynomials is the sum of lists. -/
instance : Add (Poly R) := ⟨Poly.add⟩

/-- The opposite of a polynomial is the opposite of a list. -/
instance : Neg (Poly R) := ⟨Poly.neg⟩

/-- The difference of polynomials is the difference of lists. -/
instance : Sub (Poly R) := ⟨Poly.sub⟩

/-- The product of polynomials is the product of lists. -/
instance : Mul (Poly R) := ⟨Poly.mul⟩

/-- A scalar acts on every coefficient. -/
instance {A : Type u} [SMulZeroClass A R] : SMul A (Poly R) := ⟨Poly.smul⟩

/-- The power of a polynomial, by repeated product. -/
instance : Pow (Poly R) ℕ := ⟨Poly.pow⟩

/-- A natural number is a constant polynomial. -/
instance : NatCast (Poly R) := ⟨fun n => C (n : R)⟩

/-- An integer is a constant polynomial. -/
instance : IntCast (Poly R) := ⟨fun n => C (n : R)⟩

/-- The formal derivative. -/
def derivative (p : Poly R) : Poly R :=
  Quotient.map (sa := Raw.setoid R) Raw.derivative (fun _ _ hp => Raw.derivative_congr hp) p

theorem one_def : (1 : Poly R) = C 1 := rfl

theorem ofList_add (l m : List R) : ofList l + ofList m = ofList (Raw.add l m) := rfl

theorem neg_ofList (l : List R) : -ofList l = ofList (Raw.neg l) := rfl

theorem ofList_sub (l m : List R) : ofList l - ofList m = ofList (Raw.sub l m) := rfl

theorem ofList_mul (l m : List R) : ofList l * ofList m = ofList (Raw.mul l m) := rfl

theorem smul_ofList {A : Type u} [SMulZeroClass A R] (a : A) (l : List R) :
    a • ofList l = ofList (Raw.smul a l) := rfl

theorem ofList_pow (l : List R) (n : ℕ) : ofList l ^ n = ofList (Raw.pow l n) := rfl

theorem derivative_ofList (l : List R) : (ofList l).derivative = ofList (Raw.derivative l) :=
  rfl

/-! ### The equivalence with Mathlib's polynomials -/

theorem toPolynomial_C (a : R) : (C a).toPolynomial = Polynomial.C a := Raw.toPolynomial_C a

theorem toPolynomial_X : (X : Poly R).toPolynomial = Polynomial.X := Raw.toPolynomial_X

theorem toPolynomial_monomial (n : ℕ) (a : R) :
    (monomial n a).toPolynomial = Polynomial.monomial n a := Raw.toPolynomial_monomial n a

theorem toPolynomial_one : (1 : Poly R).toPolynomial = 1 := toPolynomial_C 1

theorem toPolynomial_add (p q : Poly R) :
    (p + q).toPolynomial = p.toPolynomial + q.toPolynomial := by
  induction p, q using induction_on₂ with
  | h l m => exact Raw.toPolynomial_add l m

theorem toPolynomial_neg (p : Poly R) : (-p).toPolynomial = -p.toPolynomial := by
  induction p using induction_on with
  | h l => exact Raw.toPolynomial_neg l

theorem toPolynomial_sub (p q : Poly R) :
    (p - q).toPolynomial = p.toPolynomial - q.toPolynomial := by
  induction p, q using induction_on₂ with
  | h l m => exact Raw.toPolynomial_sub l m

theorem toPolynomial_mul (p q : Poly R) :
    (p * q).toPolynomial = p.toPolynomial * q.toPolynomial := by
  induction p, q using induction_on₂ with
  | h l m => exact Raw.toPolynomial_mul l m

theorem toPolynomial_smul {A : Type u} [SMulZeroClass A R] (a : A) (p : Poly R) :
    (a • p).toPolynomial = a • p.toPolynomial := by
  induction p using induction_on with
  | h l => exact Raw.toPolynomial_smul a l

theorem toPolynomial_pow (p : Poly R) (n : ℕ) : (p ^ n).toPolynomial = p.toPolynomial ^ n := by
  induction p using induction_on with
  | h l => exact Raw.toPolynomial_pow l n

theorem toPolynomial_natCast (n : ℕ) : (n : Poly R).toPolynomial = n :=
  (toPolynomial_C _).trans (map_natCast Polynomial.C n)

theorem toPolynomial_intCast (n : ℤ) : (n : Poly R).toPolynomial = n :=
  (toPolynomial_C _).trans (map_intCast Polynomial.C n)

/-- Every Mathlib polynomial is the polynomial of a list. -/
theorem toPolynomial_surjective : Function.Surjective (toPolynomial : Poly R → R[X]) := by
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨p, rfl⟩ := hP
    obtain ⟨q, rfl⟩ := hQ
    exact ⟨p + q, toPolynomial_add p q⟩
  | monomial n a => exact ⟨monomial n a, toPolynomial_monomial n a⟩

/-- The polynomials are a commutative ring: the laws are those of Mathlib's polynomials. -/
instance : CommRing (Poly R) :=
  fast_instance% toPolynomial_injective.commRing toPolynomial toPolynomial_zero toPolynomial_one
    toPolynomial_add toPolynomial_mul toPolynomial_neg toPolynomial_sub
    (fun n p => toPolynomial_smul n p) (fun n p => toPolynomial_smul n p)
    toPolynomial_pow toPolynomial_natCast toPolynomial_intCast

/-- The polynomials are Mathlib's polynomials. -/
noncomputable def equiv : Poly R ≃+* R[X] :=
  RingEquiv.ofBijective
    ({ toFun := toPolynomial
       map_one' := toPolynomial_one
       map_mul' := toPolynomial_mul
       map_zero' := toPolynomial_zero
       map_add' := toPolynomial_add } : Poly R →+* R[X])
    ⟨toPolynomial_injective, toPolynomial_surjective⟩

/-- The equivalence is `toPolynomial`. -/
theorem equiv_apply (p : Poly R) : equiv p = p.toPolynomial := rfl

/-! ### What the equivalence does to each operation -/

/-- The polynomial of a list is Mathlib's polynomial of that list. -/
@[simp] theorem equiv_ofList (l : List R) : equiv (ofList l) = Raw.toPolynomial l := rfl

/-- A constant polynomial is Mathlib's constant polynomial. -/
@[simp] theorem equiv_C (a : R) : equiv (C a) = Polynomial.C a := toPolynomial_C a

/-- The variable is Mathlib's variable. -/
@[simp] theorem equiv_X : equiv (X : Poly R) = Polynomial.X := toPolynomial_X

@[simp] theorem equiv_symm_C (a : R) : equiv.symm (Polynomial.C a) = C a :=
  equiv.symm_apply_eq.mpr (equiv_C a).symm

@[simp] theorem equiv_symm_X : equiv.symm (Polynomial.X : R[X]) = X :=
  equiv.symm_apply_eq.mpr equiv_X.symm

/-- `a Xⁿ` is Mathlib's monomial. -/
@[simp] theorem equiv_monomial (n : ℕ) (a : R) :
    equiv (monomial n a) = Polynomial.monomial n a := toPolynomial_monomial n a

/-- The action of a scalar on every coefficient is Mathlib's action. -/
@[simp] theorem equiv_smul {A : Type u} [SMulZeroClass A R] (a : A) (p : Poly R) :
    equiv (a • p) = a • equiv p := toPolynomial_smul a p

/-- The coefficients are those of Mathlib's polynomial. -/
@[simp] theorem coeff_equiv (p : Poly R) (n : ℕ) : (equiv p).coeff n = p.coeff n :=
  coeff_toPolynomial p n

@[simp] theorem coeff_add (p q : Poly R) (n : ℕ) : (p + q).coeff n = p.coeff n + q.coeff n := by
  simp only [← coeff_equiv, map_add, Polynomial.coeff_add]

@[simp] theorem coeff_neg (p : Poly R) (n : ℕ) : (-p).coeff n = -p.coeff n := by
  simp only [← coeff_equiv, map_neg, Polynomial.coeff_neg]

@[simp] theorem coeff_sub (p q : Poly R) (n : ℕ) : (p - q).coeff n = p.coeff n - q.coeff n := by
  simp only [← coeff_equiv, map_sub, Polynomial.coeff_sub]

@[simp] theorem coeff_smul {A : Type u} [SMulZeroClass A R] (a : A) (p : Poly R) (n : ℕ) :
    (a • p).coeff n = a • p.coeff n := by
  simp only [← coeff_equiv, equiv_smul, AddMonoidAlgebra.coeff_smul_apply]

/-- The degree is that of Mathlib's polynomial. -/
@[simp] theorem natDegree_equiv (p : Poly R) : (equiv p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [coeff_equiv, coeff_eq_zero_of_natDegree_lt hn]
    · rw [coeff_equiv, coeff_natDegree]
      exact leadingCoeff_ne_zero hp

/-- The leading coefficient is that of Mathlib's polynomial. -/
@[simp] theorem leadingCoeff_equiv (p : Poly R) : (equiv p).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_equiv, coeff_equiv, coeff_natDegree]

/-- The formal derivative is Mathlib's derivative. -/
@[simp] theorem equiv_derivative (p : Poly R) :
    equiv p.derivative = (equiv p).derivative := by
  induction p using induction_on with
  | h l => exact Raw.toPolynomial_derivative l

/-- Applying a ring homomorphism to every coefficient is Mathlib's `Polynomial.map`. -/
@[simp] theorem equiv_map {S : Type} [CommRing S] [DecidableEq S] (f : R →+* S) (p : Poly R) :
    equiv (p.map f) = (equiv p).map f := by
  induction p using induction_on with
  | h l => exact Raw.toPolynomial_map f l

/-- The value at a point is that of Mathlib's polynomial. -/
@[simp] theorem eval_equiv (x : R) (p : Poly R) : (equiv p).eval x = p.eval x := by
  induction p using induction_on with
  | h l => exact Raw.eval_toPolynomial x l

/-- The value of a polynomial is the value of its list of coefficients by Horner's rule. -/
theorem eval_eq_eval_coeffs (x : R) (p : Poly R) : p.eval x = Raw.eval x p.coeffs := by
  rw [← eval_ofList, ofList_coeffs]

/-- The image of a nonzero polynomial by an isomorphism of the coefficients is not zero. -/
theorem map_ringEquiv_ne_zero {S : Type} [CommRing S] [DecidableEq S] (e : R ≃+* S)
    {p : Poly R} (hp : p ≠ 0) : p.map e ≠ 0 := by
  intro h
  apply hp
  ext n
  have hn : e (p.coeff n) = 0 := by
    rw [← coeff_map e (map_zero e), h, coeff_zero]
  rw [coeff_zero]
  exact (map_eq_zero_iff e e.injective).mp hn

/-- The value at a natural number of the image of a polynomial by an isomorphism of the
coefficients is the image of the value. -/
theorem eval_natCast_map_ringEquiv {S : Type} [CommRing S] [DecidableEq S] (e : R ≃+* S)
    (p : Poly R) (m : ℕ) : (p.map e).eval (m : S) = e (p.eval (m : R)) := by
  have h := equiv_map (e : R →+* S) p
  rw [RingEquiv.coe_toRingHom] at h
  rw [← eval_equiv, h, Polynomial.eval_natCast_map, eval_equiv, RingEquiv.coe_toRingHom]

/-! ### Constants and the algebra structure -/

/-- The constant polynomials, as a ring homomorphism. -/
def CRingHom : R →+* Poly R where
  toFun := C
  map_one' := rfl
  map_mul' a b := equiv.injective (by simp)
  map_zero' := equiv.injective (by simp)
  map_add' a b := equiv.injective (by simp)

@[simp] theorem CRingHom_apply (a : R) : CRingHom a = C a := rfl

@[simp] theorem C_zero : C (0 : R) = 0 := map_zero CRingHom

@[simp] theorem C_one : C (1 : R) = 1 := rfl

theorem C_add (a b : R) : C (a + b) = C a + C b := map_add CRingHom a b

theorem C_mul (a b : R) : C (a * b) = C a * C b := map_mul CRingHom a b

theorem C_neg (a : R) : C (-a) = -C a := map_neg CRingHom a

theorem C_sub (a b : R) : C (a - b) = C a - C b := map_sub CRingHom a b

/-- The constant polynomials are different when the constants are. -/
theorem C_injective : Function.Injective (C : R → Poly R) := fun a b h =>
  Polynomial.C_injective (by rw [← equiv_C, ← equiv_C, h])

@[simp] theorem C_inj {a b : R} : C a = C b ↔ a = b := C_injective.eq_iff

/-- The product with a constant polynomial is the action of the constant. -/
theorem C_mul_eq_smul (a : R) (p : Poly R) : C a * p = a • p :=
  equiv.injective (by simp [Polynomial.smul_eq_C_mul])

section Algebra

variable {A : Type u} [CommSemiring A] [Algebra A R]

/-- Polynomials over an algebra are an algebra: a scalar acts on every coefficient. -/
instance : Algebra A (Poly R) where
  algebraMap := CRingHom.comp (algebraMap A R)
  commutes' _ _ := mul_comm _ _
  smul_def' a p := equiv.injective (by
    simp [Algebra.smul_def, Polynomial.algebraMap_apply])

/-- An element of the base ring is a constant polynomial. -/
theorem algebraMap_apply (a : A) : algebraMap A (Poly R) a = C (algebraMap A R a) := rfl

/-- A coefficient is a constant polynomial. -/
@[simp] theorem algebraMap_eq_C (a : R) : algebraMap R (Poly R) a = C a := rfl

/-- A scalar of the coefficients acts on a polynomial as the coefficient it is. -/
instance : IsScalarTower A R (Poly R) := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- An element of the base ring is the same constant in Mathlib's polynomials. -/
@[simp] theorem equiv_algebraMap (a : A) :
    equiv (algebraMap A (Poly R) a) = algebraMap A R[X] a := by
  rw [algebraMap_apply, equiv_C, Polynomial.algebraMap_apply]

variable (A) in
/-- The polynomials are Mathlib's polynomials, as algebras. -/
noncomputable def algEquiv : Poly R ≃ₐ[A] R[X] :=
  { equiv with commutes' := equiv_algebraMap }

@[simp] theorem algEquiv_apply (p : Poly R) : algEquiv A p = equiv p := rfl

end Algebra

/-! ### Properties inherited from the coefficients -/

/-- Polynomials over a ring with two elements are not all equal. -/
instance [Nontrivial R] : Nontrivial (Poly R) := equiv.toEquiv.nontrivial

/-- Polynomials over a domain are a domain. -/
instance [IsDomain R] : IsDomain (Poly R) := MulEquiv.isDomain R[X] equiv.toMulEquiv

/-- Polynomials have characteristic zero when the coefficients do. -/
instance [CharZero R] : CharZero (Poly R) :=
  ⟨fun m n h => by simpa using congrArg equiv h⟩

end Ring

end Poly

end SympyProofs.Calculus.Antiderivative
