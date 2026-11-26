module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split

/-! Triangular coefficient reduction for a primitive generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Prim

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Descend from the leading term. The head of the result is determined up to a constant.
The tail contains the coefficients already fixed at higher degrees. -/
def coefficients (lower : Level R n) (b : K R n) (i : ℕ) :
    List (K R n) → Option (K R n × List (K R n))
  | [] => some (0, [])
  | a :: as => do
    let (u, fixed) ← coefficients lower b (i + 1) as
    let m : K R n := (i + 1 : ℕ)
    let (c,v) ← lower.limited (a - m * b * u) b
    return (v, (u + K.ofConst c / m) :: fixed)

/-- Remove the positive powers. The output polynomial and residual `g` represent `D(P) + g`.
A solution may still add a constant multiple of the generator and subtract that multiple of
`b` from the residual before integrating in the lower field. -/
def reduce (lower : Level R n) (b : K R n) (p : Poly (K R n)) :
    Option (Poly (K R n) × K R n) := do
  let (v, fixed) ← coefficients lower b 1 p.coeffs.tail
  return (Poly.ofList (0 :: v :: fixed), p.coeff 0 - b * v)

/-- Integrate the polynomial part using the lower level's elementary combinations of the
residual and the generator derivative. A combination with nonzero residual coefficient fixes
the previously undetermined coefficient of the generator. -/
def integrate (lower : Level R n) (b : K R n) (p : Poly (K R n)) : Result R (n + 1) :=
  match reduce lower b p with
  | none => .nonelementary
  | some (q, g) =>
    match (lower.elementaryBasis [g, b]).find? (fun s => s.1.getD 0 0 != 0) with
    | none => .nonelementary
    | some (cs, a) =>
      let t := (cs.getD 0 0)⁻¹
      let correction := K.ofConst (t * cs.getD 1 0) * K.gen
      .elementary ((a.scale t).lift.addField (K.joinPoly q - correction))

end SympyProofs.Calculus.Antiderivative.Kind.Prim
