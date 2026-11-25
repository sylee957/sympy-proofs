module

public import SympyProofs.Calculus.Risch.Program.Residue
public import SympyProofs.Calculus.Risch.Proof.Poly
public import SympyProofs.Calculus.Risch.Spec.Derivation

/-! What the data of the residue step denote. A polynomial in the root variable `z` with
coefficients in the field takes a value in the field at each constant `c`. A polynomial in
the generator whose coefficients are polynomials in `z` becomes, at `c`, a polynomial in the
generator over the field. The pieces computed by the Euclidean algorithm modulo a polynomial
`m` are specified at each root of `m`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Residue

open Polynomial

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

/-- The value at the constant `c` of a polynomial in the root variable. -/
noncomputable def zeval (c : k) (p : Poly n) : K k n := (Poly.model k p).eval (constHom k n c)

/-- The polynomial in the generator obtained at the constant `c`. -/
noncomputable def bmodel (c : k) : BPoly n → (K k n)[X]
  | [] => 0
  | p :: ps => C (zeval k c p) + X * bmodel c ps

/-- Every coefficient is defined. -/
def BDefined (p : BPoly n) : Prop := ∀ q ∈ p, Poly.Defined k q

/-- The constant `c` is a root of the modulus. -/
def IsRootOf (m : Poly n) (c : k) : Prop := (Poly.model k m).IsRoot (constHom k n c)

/-- The pieces `(mⱼ, gⱼ)` describe a greatest common divisor of `a` and `b` at every root
of `m`: the moduli are defined, not zero, and multiply to `m` up to a unit, and at each
root `c` of `mⱼ` the polynomial `gⱼ(c)` divides `a(c)` and `b(c)`, is a combination of
them, and is zero or has leading coefficient one and the degree written. -/
structure PiecesOK (m : Poly n) (a b : BPoly n) (out : List (Poly n × BPoly n)) : Prop where
  defined : ∀ pc ∈ out, Poly.Defined k pc.1 ∧ BDefined k pc.2
  normal : ∀ pc ∈ out, Poly.Normal k pc.1
  prod : Associated (Poly.model k m) (out.map fun pc => Poly.model k pc.1).prod
  gcd : ∀ pc ∈ out, ∀ c : k, IsRootOf k pc.1 c →
    bmodel k c pc.2 ∣ bmodel k c a ∧ bmodel k c pc.2 ∣ bmodel k c b ∧
      (∃ u v : (K k n)[X], u * bmodel k c a + v * bmodel k c b = bmodel k c pc.2) ∧
      (pc.2 = [] ∨ ((bmodel k c pc.2).Monic ∧ (bmodel k c pc.2).natDegree = pc.2.length - 1))

variable {k}

theorem bmodel_nil (c : k) : bmodel k c ([] : BPoly n) = 0 := rfl

theorem bmodel_cons (c : k) (p : Poly n) (ps : BPoly n) :
    bmodel k c (p :: ps) = C (zeval k c p) + X * bmodel k c ps := rfl

theorem bdefined_nil : BDefined k ([] : BPoly n) := fun _ h => by cases h

theorem bdefined_cons {p : Poly n} {ps : BPoly n} :
    BDefined k (p :: ps) ↔ Poly.Defined k p ∧ BDefined k ps := by
  simp [BDefined]

end SympyProofs.Calculus.Risch.Residue
