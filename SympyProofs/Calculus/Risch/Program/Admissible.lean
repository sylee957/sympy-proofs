module

public import SympyProofs.Calculus.Risch.Program.Solve

/-! The test for admissible towers, one generator at a time. A primitive of `b` is accepted
when `b` is defined and `y′ = b` has no solution in the field below. An exponential of `u`
is accepted when `u` is defined and `u′` lies outside the space of `relRows`.

Above the first generator a primitive is required to be written as a logarithm, with
`b = u′ / u`. The variable is the primitive of a nonzero constant over the constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- The term has the form `u′ / u` for the derivation of the tower. -/
def Tower.isLog {n : Nat} (t : Tower n) : Term n → Bool
  | .div d u => d == t.D u
  | _ => false

/-- Every generator of the tower is transcendental over the field below it and adds no
constant, and every primitive above the constant field is a logarithm. -/
def admissible : {n : Nat} → Tower n → Bool
  | _, .const => true
  | _, .prim (n := n) t b =>
    admissible t && b.defined && (rde t (.const 0) b).isNone && (n == 0 || t.isLog b)
  | _, .exp t u => admissible t && u.defined && Rel.expOk t u

end SympyProofs.Calculus.Risch
