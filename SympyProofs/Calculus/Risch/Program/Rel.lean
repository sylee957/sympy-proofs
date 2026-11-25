module

public import SympyProofs.Calculus.Risch.Program.Deriv
public import SympyProofs.Calculus.Risch.Program.Constraints
public import SympyProofs.Calculus.Risch.Program.Linear

/-! A linear system over the rationals for the constants `αᵢ` such that `Σ αᵢ wᵢ` lies in a
space that contains every logarithmic derivative of the field: at most simple poles, no pole
at an exponential generator, and a constant term of the same kind one level down, up to a
multiple of the derivative of the exponent. It decides for which integer `m` an element
`g + m u′` can be a logarithmic derivative, and whether a new exponential is admissible. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Poly

/-- Numerators of the terms over one common denominator. -/
def commonDen : List (Term (n + 1)) → List (Poly n) × Poly n
  | [] => ([], [.const 1])
  | g :: gs =>
    (mul (ofTerm g).1 (commonDen gs).2 :: (commonDen gs).1.map fun W => mul W (ofTerm g).2,
      mul (ofTerm g).2 (commonDen gs).2)

end Poly

namespace Rel

open Poly

/-- Remainders of the numerators by the greatest common divisor `G` of the common
denominator `T` and its derivative, and polynomial parts of the fractions over `T / G`.
With `atX` the derivative is multiplied by the generator, which forbids a pole there. -/
def parts (atX : Bool) (ws : List (Term (n + 1))) : List (Poly n) × List (Poly n) :=
  let cm := commonDen ws
  let T := trim (norm cm.2)
  let dT := if atX then .const 0 :: formalD T else formalD T
  let G := trim (norm (gcd T dT).1)
  let Ts := trim (norm (quot T G))
  (cm.1.map fun W => rem W G, cm.1.map fun W => quot (quot W G) Ts)

/-- The rows at one step, and the constant terms left for the preceding field. -/
def stepRows (atX : Bool) (ws : List (Term (n + 1))) : List (List Rat) × List (Term n) :=
  let pr := parts atX ws
  (rowsOf (pr.1.map toTerm) ++ rowsOf (pr.2.map fun A => toTerm A.tail),
    pr.2.map fun A => coeff A 0)

end Rel

/-- The linear system over the rationals for membership of a combination in the space. -/
def relRows : {n : Nat} → Tower n → List (Term n) → List (List Rat)
  | _, .const, ws => rowsOf ws
  | _, .prim t _, ws =>
    let sr := Rel.stepRows false ws
    sr.1 ++ relRows t sr.2
  | _, .exp t u, ws =>
    let sr := Rel.stepRows true ws
    sr.1 ++ Linear.eliminate ws.length (relRows t (sr.2 ++ [t.D u]))

namespace Rel

/-- The largest `m` for which some row with a nonzero second entry vanishes on `(1, m)`. -/
def exponent (rows : List (List Rat)) : Nat :=
  rows.foldr (fun r acc =>
    if r.getD 1 0 == 0 then acc else max acc (-(r.getD 0 0) / r.getD 1 0).ceil.toNat) 0

/-- An upper bound for the integers `m` such that `g + m u′` is a logarithmic derivative in
the field of `t`, where the exponential of `u` is admissible over `t`. -/
def exponentBound (t : Tower n) (u g : Term n) : Nat := exponent (relRows t [g, t.D u])

/-- No positive multiple of `u′` is a logarithmic derivative in the field of `t`. -/
def expOk (t : Tower n) (u : Term n) : Bool :=
  (relRows t [t.D u]).any fun r => Linear.dot r [1] != 0

end Rel

end SympyProofs.Calculus.Risch
