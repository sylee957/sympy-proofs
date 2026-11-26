module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Raw
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Semantics
public import Mathlib.RingTheory.Localization.FractionRing

/-! Flat fractions modulo equality of their values in Mathlib's field of fractions. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace K.Raw

variable {R : Type} [CommRing R] [IsDomain R] (n : ℕ)

/-- Interpret a sparse polynomial in the fraction field of the model. -/
noncomputable def polyValue (p : MPoly.Raw R) : FractionRing (MvPolynomial (Fin n) R) :=
  algebraMap _ _ (MPoly.Raw.toMvPolynomial n p)

/-- Divide the polynomial values, using the field convention for a zero denominator. -/
noncomputable def value (x : K.Raw R) : FractionRing (MvPolynomial (Fin n) R) :=
  polyValue n x.num / polyValue n x.den

variable (R) in
/-- Identify exactly the pairs with the same field value. -/
def setoid : Setoid (K.Raw R) :=
  ⟨fun x y => value n x = value n y, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

end K.Raw

/-- Rational functions in the first `n` generators, represented by one flat fraction. -/
def K (R : Type) (n : ℕ) [CommRing R] [IsDomain R] := Quotient (K.Raw.setoid R n)

namespace K

variable {R : Type} [CommRing R] [IsDomain R] {n : ℕ}

/-- The field element represented by a pair of sparse polynomials. -/
def ofRaw (x : Raw R) : K R n := Quotient.mk _ x

/-- Interpret an element of the flat field in Mathlib's fraction field. -/
noncomputable def toFractionRing : K R n → FractionRing (MvPolynomial (Fin n) R) :=
  Quotient.lift (s := Raw.setoid R n) (Raw.value n) fun _ _ h => h

@[simp] theorem toFractionRing_ofRaw (x : Raw R) :
    toFractionRing (ofRaw x : K R n) = Raw.value n x := rfl

/-- The model distinguishes all elements of the quotient. -/
theorem toFractionRing_injective : Function.Injective (toFractionRing (R := R) (n := n)) := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact Quotient.sound h

end K

end SympyProofs.Calculus.Antiderivative
