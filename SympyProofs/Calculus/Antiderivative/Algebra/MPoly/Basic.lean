module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Canonical
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.FastInstance

/-! The quotient ring of sparse multivariate polynomials, with list arithmetic. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Term lists are equivalent when their coefficient functions in the first `n` variables agree. -/
def MPoly.Raw.setoid (n : ℕ) (R : Type*) [AddCommMonoid R] : Setoid (MPoly.Raw R) :=
  ⟨fun p q => MPoly.Raw.value n p = MPoly.Raw.value n q, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

/-- Sparse polynomials in `n` variables over `R`, represented by lists of terms. -/
def MPoly (n : ℕ) (R : Type*) [AddCommMonoid R] := Quotient (MPoly.Raw.setoid n R)

namespace MPoly

variable {n : ℕ} {R : Type*}

section Add

variable [AddCommMonoid R]

/-- Construct a polynomial from any list of terms. -/
def ofRaw (p : Raw R) : MPoly n R := Quotient.mk (Raw.setoid n R) p

theorem ofRaw_eq_iff {p q : Raw R} :
    ofRaw (n := n) p = ofRaw q ↔ Raw.value n p = Raw.value n q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Every polynomial is represented by a term list. -/
@[elab_as_elim] theorem induction_on {P : MPoly n R → Prop} (p : MPoly n R)
    (h : ∀ a, P (ofRaw a)) : P p := Quotient.inductionOn p h

/-- Every pair of polynomials is represented by two term lists. -/
@[elab_as_elim] theorem induction_on₂ {P : MPoly n R → MPoly n R → Prop} (p q : MPoly n R)
    (h : ∀ a b, P (ofRaw a) (ofRaw b)) : P p q := Quotient.inductionOn₂ p q h

instance : Zero (MPoly n R) := ⟨ofRaw []⟩
instance : Inhabited (MPoly n R) := ⟨0⟩

@[simp] theorem ofRaw_nil : ofRaw (n := n) ([] : Raw R) = 0 := rfl

variable [DecidableEq R]

/-- Comparing sorted term lists decides polynomial equality. -/
theorem normalize_eq_iff {p q : Raw R} :
    Raw.normalize n p = Raw.normalize n q ↔ ofRaw (n := n) p = ofRaw q := by
  rw [ofRaw_eq_iff, Raw.normalize_eq_iff_value]

/-- The unique sorted list of nonzero terms. -/
def terms (p : MPoly n R) : Raw R :=
  Quotient.lift (s := Raw.setoid n R) (Raw.normalize n)
    (fun a b => (Raw.normalize_eq_iff_value n a b).mpr) p

@[simp] theorem terms_ofRaw (p : Raw R) : (ofRaw (n := n) p).terms = Raw.normalize n p := rfl

@[simp] theorem ofRaw_normalize (p : Raw R) : ofRaw (Raw.normalize n p) = ofRaw (n := n) p :=
  ofRaw_eq_iff.mpr (Raw.value_normalize n p)

@[simp] theorem ofRaw_terms (p : MPoly n R) : ofRaw p.terms = p := by
  induction p using induction_on with | h a => exact ofRaw_normalize a

instance : DecidableEq (MPoly n R) := fun p q =>
  decidable_of_iff (p.terms = q.terms)
    ⟨fun h => by simpa using congrArg (ofRaw (n := n)) h, congrArg terms⟩

/-- The constant polynomial with coefficient `c`. -/
def C (c : R) : MPoly n R := ofRaw (Raw.C c)

@[simp] theorem ofRaw_C (c : R) : ofRaw (n := n) (Raw.C c) = C c := rfl

end Add

section Ring

variable [CommRing R]

/-- Mathlib's polynomial with exactly the coefficients of this polynomial. -/
noncomputable def toMvPolynomial (p : MPoly n R) : MvPolynomial (Fin n) R :=
  Quotient.lift (s := Raw.setoid n R) (Raw.toMvPolynomial n)
    (fun _ _ h => congrArg AddMonoidAlgebra.ofCoeff h) p

@[simp] theorem toMvPolynomial_ofRaw (a : Raw R) :
    (ofRaw a).toMvPolynomial = Raw.toMvPolynomial n a := rfl

theorem raw_eq_iff (a b : Raw R) :
    (Raw.setoid n R).r a b ↔ Raw.toMvPolynomial n a = Raw.toMvPolynomial n b :=
  AddMonoidAlgebra.ofCoeff_inj.symm

theorem toMvPolynomial_injective : Function.Injective (toMvPolynomial (n := n) (R := R)) := by
  intro p q
  induction p, q using induction_on₂ with
  | h a b => exact fun h => Quotient.sound ((raw_eq_iff a b).mpr h)

theorem toMvPolynomial_zero : (0 : MPoly n R).toMvPolynomial = 0 := rfl

variable [DecidableEq R]

/-- The variable with index `i`, giving zero when `i` lies outside the tower. -/
def X (i : ℕ) : MPoly n R := ofRaw (Raw.X n i)

@[simp] theorem ofRaw_X (i : ℕ) : ofRaw (Raw.X n i : Raw R) = X (n := n) i := rfl

instance : One (MPoly n R) := ⟨C 1⟩

instance : Add (MPoly n R) where
  add := Quotient.map₂ (Raw.add n) fun a a' ha b b' hb =>
    (raw_eq_iff _ _).mpr (by simp [(raw_eq_iff a a').mp ha, (raw_eq_iff b b').mp hb])

instance : Neg (MPoly n R) where
  neg := Quotient.map (Raw.neg n) fun a a' ha =>
    (raw_eq_iff _ _).mpr (by simp [(raw_eq_iff a a').mp ha])

instance : Mul (MPoly n R) where
  mul := Quotient.map₂ (Raw.mul n) fun a a' ha b b' hb =>
    (raw_eq_iff _ _).mpr (by simp [(raw_eq_iff a a').mp ha, (raw_eq_iff b b').mp hb])

instance : Sub (MPoly n R) := ⟨fun p q => p + -q⟩
instance : NatCast (MPoly n R) := ⟨fun m => C (m : R)⟩
instance : IntCast (MPoly n R) := ⟨fun m => C (m : R)⟩
instance : SMul ℕ (MPoly n R) := ⟨fun m p => C (m : R) * p⟩
instance : SMul ℤ (MPoly n R) := ⟨fun m p => C (m : R) * p⟩
instance : Pow (MPoly n R) ℕ := ⟨fun p m => Nat.rec 1 (fun _ a => a * p) m⟩

@[simp] theorem ofRaw_add (a b : Raw R) :
    ofRaw (Raw.add n a b) = ofRaw (n := n) a + ofRaw b := rfl

@[simp] theorem ofRaw_neg (a : Raw R) : ofRaw (Raw.neg n a) = -ofRaw (n := n) a := rfl

@[simp] theorem ofRaw_mul (a b : Raw R) :
    ofRaw (Raw.mul n a b) = ofRaw (n := n) a * ofRaw b := rfl

@[simp] theorem toMvPolynomial_C (c : R) :
    (C c : MPoly n R).toMvPolynomial = MvPolynomial.C c := Raw.toMvPolynomial_C n c

theorem toMvPolynomial_one : (1 : MPoly n R).toMvPolynomial = 1 :=
  (toMvPolynomial_C _).trans (map_one MvPolynomial.C)

theorem toMvPolynomial_add (p q : MPoly n R) :
    (p + q).toMvPolynomial = p.toMvPolynomial + q.toMvPolynomial := by
  induction p, q using induction_on₂ with | h a b => exact Raw.toMvPolynomial_add n a b

theorem toMvPolynomial_neg (p : MPoly n R) :
    (-p).toMvPolynomial = -p.toMvPolynomial := by
  induction p using induction_on with | h a => exact Raw.toMvPolynomial_neg n a

theorem toMvPolynomial_mul (p q : MPoly n R) :
    (p * q).toMvPolynomial = p.toMvPolynomial * q.toMvPolynomial := by
  induction p, q using induction_on₂ with | h a b => exact Raw.toMvPolynomial_mul n a b

theorem toMvPolynomial_pow (p : MPoly n R) (m : ℕ) :
    (p ^ m).toMvPolynomial = p.toMvPolynomial ^ m := by
  induction m with
  | zero => rw [pow_zero]; exact toMvPolynomial_one
  | succ m ih => exact (toMvPolynomial_mul (p ^ m) p).trans (by rw [ih, pow_succ])

/-- All ring operations on the quotient are the computable operations on lists. -/
instance : CommRing (MPoly n R) :=
  fast_instance% toMvPolynomial_injective.commRing toMvPolynomial toMvPolynomial_zero
    toMvPolynomial_one toMvPolynomial_add toMvPolynomial_mul toMvPolynomial_neg
    (fun p q => (toMvPolynomial_add p (-q)).trans (by rw [toMvPolynomial_neg, sub_eq_add_neg]))
    (fun m p => (toMvPolynomial_mul (C (m : R)) p).trans (by simp [nsmul_eq_mul]))
    (fun m p => (toMvPolynomial_mul (C (m : R)) p).trans (by simp [zsmul_eq_mul]))
    toMvPolynomial_pow (fun m => (toMvPolynomial_C _).trans (map_natCast MvPolynomial.C m))
    (fun m => (toMvPolynomial_C _).trans (map_intCast MvPolynomial.C m))

/-- Every polynomial in `Fin n` is represented by a list of monomials. -/
theorem toMvPolynomial_surjective : Function.Surjective (toMvPolynomial (n := n) (R := R)) := by
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    let e : Mono := List.ofFn fun i : Fin n => s i
    have he : e.trim.length ≤ n := (Mono.fits_iff n e).mpr fun j hj =>
      Poly.Raw.coeff_eq_zero_of_length_le (by simpa [e] using hj)
    have hs : e.exponents n = s := by
      ext i
      simp [e, Poly.Raw.coeff, List.getD_eq_getElem?_getD]
    exact ⟨ofRaw [(e,a)], by simp [Raw.toMvPolynomial_cons, he, hs]⟩
  | add p q hp hq =>
    obtain ⟨a,rfl⟩ := hp
    obtain ⟨b,rfl⟩ := hq
    exact ⟨a + b, toMvPolynomial_add a b⟩

/-- The ring equivalence sending a term list to its multivariate polynomial. -/
noncomputable def equiv : MPoly n R ≃+* MvPolynomial (Fin n) R :=
  RingEquiv.ofBijective
    ({ toFun := toMvPolynomial
       map_one' := toMvPolynomial_one
       map_mul' := toMvPolynomial_mul
       map_zero' := toMvPolynomial_zero
       map_add' := toMvPolynomial_add } : MPoly n R →+* MvPolynomial (Fin n) R)
    ⟨toMvPolynomial_injective, toMvPolynomial_surjective⟩

@[simp] theorem equiv_ofRaw (a : Raw R) : equiv (ofRaw a) = Raw.toMvPolynomial n a := rfl

@[simp] theorem equiv_C (c : R) : equiv (C c : MPoly n R) = MvPolynomial.C c :=
  toMvPolynomial_C c

/-- The inclusion of the coefficient ring as constant polynomials. -/
def CRingHom : R →+* MPoly n R where
  toFun := C
  map_one' := rfl
  map_zero' := equiv.injective (by simp)
  map_mul' _ _ := equiv.injective (by simp)
  map_add' _ _ := equiv.injective (by simp)

instance : Algebra R (MPoly n R) := CRingHom.toAlgebra

@[simp] theorem algebraMap_eq_C (c : R) : algebraMap R (MPoly n R) c = C c := rfl

instance [Nontrivial R] : Nontrivial (MPoly n R) := equiv.toEquiv.nontrivial

instance [IsDomain R] : IsDomain (MPoly n R) :=
  MulEquiv.isDomain (MvPolynomial (Fin n) R) equiv.toMulEquiv

end Ring

end MPoly

end SympyProofs.Calculus.Antiderivative
