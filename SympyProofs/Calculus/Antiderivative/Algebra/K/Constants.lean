module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Basic
public import SympyProofs.Calculus.Antiderivative.Algebra.Rat
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! The field at height zero is the fraction field of the coefficient ring. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R]

/-- Sum the coefficients of terms with no positive exponent. -/
def MPoly.Raw.constantTerm : MPoly.Raw R → R
  | [] => 0
  | (e, c) :: p => (if e.trim.length = 0 then c else 0) + constantTerm p

/-- A sparse polynomial in zero variables is its constant coefficient. -/
theorem MPoly.Raw.toMvPolynomial_zero_vars (p : MPoly.Raw R) :
    p.toMvPolynomial 0 = MvPolynomial.C p.constantTerm := by
  induction p with
  | nil => simp [constantTerm]
  | cons t p ih =>
    rcases t with ⟨e, c⟩
    have he : Mono.exponents 0 e = 0 := Subsingleton.elim _ _
    simp [toMvPolynomial_cons, constantTerm, ih, he, apply_ite, MvPolynomial.monomial_zero']

namespace K

variable [IsDomain R] (Γ : Type) [Field Γ] [Algebra R Γ] [IsFractionRing R Γ]

/-- Removing the empty set of variables identifies the two fraction fields. -/
noncomputable def modelConstantsEquiv : FractionRing (MvPolynomial (Fin 0) R) ≃+* Γ :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0))

/-- Read the numerator and denominator of a height-zero fraction in the coefficient field. -/
def Raw.constantValue (p : Raw R) : Γ :=
  algebraMap R Γ p.num.constantTerm / algebraMap R Γ p.den.constantTerm

/-- Evaluating the raw numerator and denominator gives their quotient in the fraction field. -/
theorem Raw.constantValue_eq (p : Raw R) :
    p.constantValue Γ = modelConstantsEquiv Γ (p.value 0) := by
  rw [Raw.value, Raw.polyValue, Raw.polyValue, modelConstantsEquiv, map_div₀,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, MPoly.Raw.toMvPolynomial_zero_vars,
    MPoly.Raw.toMvPolynomial_zero_vars, Raw.constantValue]
  simp only [← MvPolynomial.isEmptyRingEquiv_symm_apply, RingEquiv.apply_symm_apply]

/-- Evaluate a height-zero fraction in a fraction field of its coefficient ring. -/
def toConstants (x : K R 0) : Γ :=
  Quotient.liftOn x (Raw.constantValue Γ) fun a b h => by
    rw [Raw.constantValue_eq, Raw.constantValue_eq]
    exact congrArg (modelConstantsEquiv Γ) h

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Reading the coefficients agrees with the fraction field isomorphism. -/
theorem toConstants_eq (x : K R 0) :
    toConstants Γ x = (equiv.trans (modelConstantsEquiv Γ)) x := by
  induction x using Quotient.inductionOn with
  | _ p => exact Raw.constantValue_eq Γ p

/-- The height-zero field is isomorphic to every fraction field of its coefficient ring. -/
noncomputable def constantsEquiv : K R 0 ≃+* Γ where
  toFun := toConstants Γ
  invFun := (equiv.trans (modelConstantsEquiv Γ)).symm
  left_inv x := by rw [toConstants_eq, RingEquiv.symm_apply_apply]
  right_inv x := by rw [toConstants_eq, RingEquiv.apply_symm_apply]
  map_add' x y := by rw [toConstants_eq, map_add, ← toConstants_eq, ← toConstants_eq]
  map_mul' x y := by rw [toConstants_eq, map_mul, ← toConstants_eq, ← toConstants_eq]

/-- Bounds for a height-zero fraction of integers, computed on its rational value. -/
instance natBoundInt : NatBound (K ℤ 0) := NatBound.ofMap (toConstants ℚ)

/-- Bounds for a height-zero fraction of field elements, computed in that field. -/
instance natBoundField {F : Type} [Field F] [DecidableEq F] [NatBound F] :
    NatBound (K F 0) := NatBound.ofMap (toConstants F)

end K

end SympyProofs.Calculus.Antiderivative
