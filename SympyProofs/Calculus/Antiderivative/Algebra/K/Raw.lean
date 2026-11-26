module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Raw

/-! Arithmetic on a single pair of sparse polynomials in all the generators. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- A fraction of sparse polynomials. A zero denominator represents zero. -/
structure K.Raw (R : Type) where
  /-- The numerator. -/
  num : MPoly.Raw R
  /-- The denominator. -/
  den : MPoly.Raw R
  deriving Repr

namespace K.Raw

variable {R : Type} [CommRing R] [DecidableEq R]

/-- A polynomial with denominator one. -/
def ofPoly (p : MPoly.Raw R) : Raw R := ⟨p, MPoly.Raw.C 1⟩

/-- A coefficient as a fraction. -/
def C (a : R) : Raw R := ofPoly (MPoly.Raw.C a)

/-- Test polynomial equality, skipping normalization for identical lists. -/
def polyEq (n : ℕ) (p q : MPoly.Raw R) : Bool :=
  p == q || MPoly.Raw.normalize n p == MPoly.Raw.normalize n q

/-- A fraction vanishes if either part vanishes. -/
def isZero (n : ℕ) (x : Raw R) : Bool := polyEq n x.num [] || polyEq n x.den []

/-- Equality by cross multiplication, with short paths for zero and equal denominators. -/
def beq (n : ℕ) (x y : Raw R) : Bool :=
  if isZero n x then isZero n y
  else if isZero n y then false
  else if polyEq n x.den y.den then polyEq n x.num y.num
  else polyEq n (MPoly.Raw.mul n x.num y.den) (MPoly.Raw.mul n y.num x.den)

/-- Negate the numerator. -/
def neg (n : ℕ) (x : Raw R) : Raw R := ⟨MPoly.Raw.neg n x.num, x.den⟩

/-- Invert by exchanging the two parts, including for representatives of zero. -/
def inv (x : Raw R) : Raw R := ⟨x.den, x.num⟩

variable [NormalizedGCDMonoid R] [Div R]

/-- Cancel a candidate common divisor only when both exact divisions succeed. -/
def cancel (n : ℕ) (a b : MPoly.Raw R) : Raw R :=
  if polyEq n b (MPoly.Raw.C 1) then ⟨a, b⟩
  else if polyEq n a [] || polyEq n b [] then ofPoly []
  else
    let g := MPoly.Raw.commonDivisor n a b
    if polyEq n g (MPoly.Raw.C 1) then ⟨a, b⟩
    else
      match MPoly.Raw.divExact? n a g, MPoly.Raw.divExact? n b g with
      | some a', some b' => ⟨a', b'⟩
      | _, _ => ⟨a, b⟩

/-- Remove a checked common factor, returning the two quotients and the removed factor. -/
def factorPair (n : ℕ) (a b : MPoly.Raw R) : MPoly.Raw R × MPoly.Raw R × MPoly.Raw R :=
  let one := MPoly.Raw.C (1 : R)
  if polyEq n a one || polyEq n b one then (a, b, one)
  else
    let g := MPoly.Raw.commonDivisor n a b
    if polyEq n g one then (a, b, one)
    else
      match MPoly.Raw.divExact? n a g, MPoly.Raw.divExact? n b g with
      | some u, some v => (u, v, g)
      | _, _ => (a, b, one)

/-- Add fractions, sharing a common denominator when the two already agree. -/
def add (n : ℕ) (x y : Raw R) : Raw R :=
  if isZero n x then y
  else if isZero n y then x
  else if polyEq n x.den y.den then cancel n (MPoly.Raw.add n x.num y.num) x.den
  else
    let (b, d, g) := factorPair n x.den y.den
    let t := MPoly.Raw.add n (MPoly.Raw.mul n x.num d) (MPoly.Raw.mul n y.num b)
    let (u, v, _) := factorPair n t g
    ⟨u, MPoly.Raw.mul n b (MPoly.Raw.mul n d v)⟩

/-- Multiply fractions, cancelling each numerator against the opposite denominator first. -/
def mul (n : ℕ) (x y : Raw R) : Raw R :=
  let a := cancel n x.num y.den
  let b := cancel n y.num x.den
  ⟨MPoly.Raw.mul n a.num b.num, MPoly.Raw.mul n a.den b.den⟩

end K.Raw

end SympyProofs.Calculus.Antiderivative
