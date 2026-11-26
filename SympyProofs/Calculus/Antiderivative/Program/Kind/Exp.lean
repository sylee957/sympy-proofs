module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split

/-! Integrate Laurent polynomials in an exponential generator, one coefficient at a time. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Exp

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Solve the coefficient equations for powers of the generator, leaving its zeroth power
for integration in the lower field. The input list starts at exponent `j - k`. -/
def coefficients (lower : Level R n) (du : K R n) (k j : ℕ) :
    List (K R n) → Option (List (K R n))
  | [] => some []
  | a :: as => do
    let b ← if j = k then some 0 else lower.rde (((j : K R n) - k) * du) a
    return b :: (← coefficients lower du k (j + 1) as)

/-- Integrate the Laurent polynomial `p/θᵏ` when `θ′ = u′ θ`. -/
def integrate (D : K R n → K R n) (u : K R n) (lower : Level R n) (p : Poly (K R n)) (k : ℕ) :
    Result R (n + 1) :=
  match coefficients lower (D u) k 0 p.coeffs with
  | none => .nonelementary
  | some cs =>
    match lower.integrate (p.coeff k) with
    | .nonelementary => .nonelementary
    | .elementary a =>
      .elementary (a.lift.addField (K.joinPoly (Poly.ofList cs) / K.gen ^ k))

end SympyProofs.Calculus.Antiderivative.Kind.Exp
