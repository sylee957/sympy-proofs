module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Raw

/-! Arithmetic directly on the coefficients of fractions that consist of constant terms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.K.Raw

variable {R : Type} [CommRing R]

/-- Read an empty polynomial or a single constant term from its list representation. -/
@[inline] def scalar? : MPoly.Raw R → Option R
  | [] => some 0
  | [([], c)] => some c
  | _ => none

/-- Read a pair of scalar polynomials in any number of variables. -/
@[inline] def scalars? (x : Raw R) : Option (R × R) := do
  return (← scalar? x.num, ← scalar? x.den)

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Represent a coefficient ratio as a flat fraction. -/
@[inline] def scalarFraction (a b : R) : Raw R := ⟨MPoly.Raw.C a, MPoly.Raw.C b⟩

/-- Cancel the coefficient gcd after checking both quotients in the coefficient ring. -/
def reduceScalars (a b : R) : Raw R :=
  if b = 1 then C a
  else if a = 0 || b = 0 then C 0
  else if a / b * b = a then C (a / b)
  else
    let g := gcd a b
    if g = 1 then scalarFraction a b
    else
      let u := a / g
      let v := b / g
      if u * g = a && v * g = b then scalarFraction u v else scalarFraction a b

/-- Use coefficient arithmetic for the sum when both pairs consist of constants. -/
def addScalars (n : ℕ) (x y : Raw R) : Raw R :=
  match x.scalars?, y.scalars? with
  | some (a,b), some (c,d) =>
    if b = 0 then y
    else if d = 0 then x
    else if b = d then reduceScalars (a + c) b
    else reduceScalars (a * d + c * b) (b * d)
  | _, _ => add n x y

/-- Use coefficient arithmetic for the product when both pairs consist of constants. -/
def mulScalars (n : ℕ) (x y : Raw R) : Raw R :=
  match x.scalars?, y.scalars? with
  | some (a,b), some (c,d) => reduceScalars (a * c) (b * d)
  | _, _ => mul n x y

end SympyProofs.Calculus.Antiderivative.K.Raw
