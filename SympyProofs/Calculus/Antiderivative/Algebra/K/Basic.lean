module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Scalar
public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Basic
public import Mathlib.Algebra.CharP.Algebra

/-! The computable field of flat fractions and its identification with a fraction field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K

variable {R : Type} [CommRing R] [IsDomain R] {n : ℕ} [DecidableEq R]

/-- Decide equality by testing representatives in the flat representation. -/
instance : DecidableEq (K R n) :=
  @Quotient.decidableEq _ (Raw.setoid R n) fun x y => decidable_of_iff _ (Raw.beq_iff n x y)

/-- A coefficient with denominator one at any height. -/
def C (a : R) : K R n := ofRaw (Raw.C a)

@[simp] theorem toFractionRing_C (a : R) :
    toFractionRing (C a : K R n) = algebraMap (MvPolynomial (Fin n) R) _ (MvPolynomial.C a) :=
  Raw.value_C n a

local instance : Zero (K R n) := ⟨C 0⟩
local instance : One (K R n) := ⟨C 1⟩
local instance : Neg (K R n) where
  neg := Quotient.map (Raw.neg n) fun x y (h : Raw.value n x = Raw.value n y) => by
    change Raw.value n _ = Raw.value n _
    simp [h]
local instance : Inv (K R n) where
  inv := Quotient.map Raw.inv fun x y (h : Raw.value n x = Raw.value n y) => by
    change Raw.value n _ = Raw.value n _
    simp [h]

variable [NormalizedGCDMonoid R] [Div R]

local instance : Add (K R n) where
  add := Quotient.map₂ (Raw.addScalars n) fun x x' hx y y' hy => by
    change Raw.value n _ = Raw.value n _
    simp only [Raw.value_addScalars]
    exact congrArg₂ (· + ·) hx hy
local instance : Mul (K R n) where
  mul := Quotient.map₂ (Raw.mulScalars n) fun x x' hx y y' hy => by
    change Raw.value n _ = Raw.value n _
    simp only [Raw.value_mulScalars]
    exact congrArg₂ (· * ·) hx hy

omit [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem toFractionRing_zero : toFractionRing (0 : K R n) = 0 := by
  change toFractionRing (C 0 : K R n) = _
  simp

omit [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem toFractionRing_one : toFractionRing (1 : K R n) = 1 := by
  change toFractionRing (C 1 : K R n) = _
  simp

@[simp] theorem toFractionRing_add (x y : K R n) :
    toFractionRing (x + y) = toFractionRing x + toFractionRing y :=
  Quotient.inductionOn₂ x y (Raw.value_addScalars n)

@[simp] theorem toFractionRing_mul (x y : K R n) :
    toFractionRing (x * y) = toFractionRing x * toFractionRing y :=
  Quotient.inductionOn₂ x y (Raw.value_mulScalars n)

omit [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem toFractionRing_neg (x : K R n) : toFractionRing (-x) = -toFractionRing x :=
  Quotient.inductionOn x (Raw.value_neg n)

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem toFractionRing_inv (x : K R n) : toFractionRing x⁻¹ = (toFractionRing x)⁻¹ :=
  Quotient.inductionOn x (Raw.value_inv n)

/-- Arithmetic on the quotient satisfies the field laws through its injective interpretation. -/
instance : Field (K R n) where
  add_assoc _ _ _ := toFractionRing_injective (by simp [add_assoc])
  add_comm _ _ := toFractionRing_injective (by simp [add_comm])
  add_zero _ := toFractionRing_injective (by simp)
  zero_add _ := toFractionRing_injective (by simp)
  mul_assoc _ _ _ := toFractionRing_injective (by simp [mul_assoc])
  mul_comm _ _ := toFractionRing_injective (by simp [mul_comm])
  one_mul _ := toFractionRing_injective (by simp)
  mul_one _ := toFractionRing_injective (by simp)
  mul_zero _ := toFractionRing_injective (by simp)
  zero_mul _ := toFractionRing_injective (by simp)
  left_distrib _ _ _ := toFractionRing_injective (by simp [mul_add])
  right_distrib _ _ _ := toFractionRing_injective (by simp [add_mul])
  neg_add_cancel _ := toFractionRing_injective (by simp)
  exists_pair_ne := ⟨0, 1, fun h => (zero_ne_one (α := FractionRing (MvPolynomial (Fin n) R)))
    (by simpa using congrArg toFractionRing h)⟩
  mul_inv_cancel a ha := toFractionRing_injective (by
    have h : toFractionRing a ≠ 0 := fun h => ha (toFractionRing_injective (h.trans
      toFractionRing_zero.symm))
    simp [h])
  inv_zero := toFractionRing_injective (by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast k := C (k : R)
  natCast_zero := congrArg C (Nat.cast_zero (R := R))
  natCast_succ k := toFractionRing_injective (by simp)
  intCast k := C (k : R)
  intCast_ofNat k := congrArg C (Int.cast_natCast (R := R) k)
  intCast_negSucc k := toFractionRing_injective (by
    change toFractionRing (C (Int.negSucc k : R) : K R n) = toFractionRing (-(C _)); simp)
  nnqsmul := _
  qsmul := _

/-- View a field element as a ring homomorphism value in the model. -/
noncomputable def modelHom : K R n →+* FractionRing (MvPolynomial (Fin n) R) where
  toFun := toFractionRing
  map_zero' := toFractionRing_zero
  map_one' := toFractionRing_one
  map_add' := toFractionRing_add
  map_mul' := toFractionRing_mul

/-- Embedding of the ring of sparse polynomials into the flat field. -/
def ofPoly : MPoly n R →+* K R n where
  toFun p := ofRaw (Raw.ofPoly p.terms)
  map_zero' := toFractionRing_injective (by simp [Raw.polyValue, ← MPoly.equiv_ofRaw])
  map_one' := toFractionRing_injective (by simp [Raw.polyValue, ← MPoly.equiv_ofRaw])
  map_add' _ _ := toFractionRing_injective (by simp [Raw.polyValue, ← MPoly.equiv_ofRaw])
  map_mul' _ _ := toFractionRing_injective (by simp [Raw.polyValue, ← MPoly.equiv_ofRaw])

@[simp] theorem toFractionRing_ofPoly (p : MPoly n R) :
    toFractionRing (ofPoly p) = algebraMap _ _ (MPoly.equiv p) := by
  change Raw.value n (Raw.ofPoly p.terms) = _
  simp [Raw.polyValue, ← MPoly.equiv_ofRaw]

instance : Algebra (MPoly n R) (K R n) := ofPoly.toAlgebra

/-- Raw pairs are quotients of the images of their two polynomials. -/
theorem ofRaw_eq_div (x : Raw R) :
    (ofRaw x : K R n) = ofPoly (MPoly.ofRaw x.num) / ofPoly (MPoly.ofRaw x.den) := by
  apply modelHom.injective
  rw [map_div₀]
  change Raw.value n x = toFractionRing (ofPoly _) / toFractionRing (ofPoly _)
  simp [Raw.value, Raw.polyValue]

instance : IsFractionRing (MPoly n R) (K R n) := by
  let : FaithfulSMul (MPoly n R) (K R n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h => by
      change ofPoly a = ofPoly b at h
      have he := congrArg toFractionRing h
      simp only [toFractionRing_ofPoly, (IsFractionRing.injective _ _).eq_iff] at he
      exact MPoly.equiv.injective he
  apply IsFractionRing.of_field
  rintro ⟨x⟩
  exact ⟨_, _, ofRaw_eq_div x⟩

/-- Flat fractions give every element of Mathlib's rational function field. -/
noncomputable def equiv : K R n ≃+* FractionRing (MvPolynomial (Fin n) R) :=
  RingEquiv.ofBijective modelHom ⟨toFractionRing_injective, fun z => by
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) R) z
    refine ⟨ofPoly (MPoly.equiv.symm p) / ofPoly (MPoly.equiv.symm q), ?_⟩
    rw [map_div₀]
    change toFractionRing (ofPoly _) / toFractionRing (ofPoly _) = _
    simp⟩

@[simp] theorem equiv_ofRaw (p : Raw R) : equiv (ofRaw p : K R n) = Raw.value n p := rfl

@[simp] theorem equiv_ofPoly (p : MPoly n R) :
    equiv (ofPoly p) = algebraMap _ _ (MPoly.equiv p) := toFractionRing_ofPoly p

instance [CharZero R] : CharZero (K R n) := modelHom.charZero

end SympyProofs.Calculus.Antiderivative.K
