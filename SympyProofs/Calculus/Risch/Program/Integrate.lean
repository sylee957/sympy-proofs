module

public import SympyProofs.Calculus.Risch.Program.PolyPart
public import SympyProofs.Calculus.Risch.Program.Residue
public import SympyProofs.Calculus.Risch.Program.Admissible

/-! Part (a) of Risch's Main Theorem: integration in the field of a tower, by recursion on
its depth. Over the constants only zero has a primitive. At a tower step the integrand is
reduced to a fraction with squarefree denominator and a polynomial in the generator, the
residue criterion extracts the logarithms or shows that there is no elementary integral, and
the polynomial is integrated through its coefficients. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

/-- One step of the recursion, given integration in the preceding field. -/
def integrateStep (t : Tower (n + 1)) (descend : Term n → Result n) (f : Term (n + 1)) :
    Result (n + 1) :=
  let rd := Hermite.reduceTerm t f
  let P := Poly.quot rd.Ar rd.Dr
  let A := Poly.trim (Poly.norm (Poly.rem rd.Ar rd.Dr))
  match Residue.logPart t A rd.Dr with
  | none => .nonelementary
  | some (pieces, Q) =>
    let cs := Poly.norm
      (Poly.add rd.L1 (Poly.mul (Poly.add P [Q]) (Poly.mono rd.k (.const 1))))
    match PolyPart.polyPart t descend cs rd.k with
    | .nonelementary => .nonelementary
    | .elementary a => .elementary ⟨.add rd.g a.field, a.sums ++ pieces.map Residue.toRootSum⟩

/-- Integrate a term in the field of a tower: an elementary integral, or the verdict that
there is none. -/
def integrate : {n : Nat} → Tower n → Term n → Result n
  | _, .const, f => if f.isZero then .elementary ⟨.const 0, []⟩ else .nonelementary
  | _, .prim t b, f => integrateStep (.prim t b) (integrate t) f
  | _, .exp t u, f => integrateStep (.exp t u) (integrate t) f

/-- Integrate after checking the input: the tower is admissible and the integrand is
defined in its field. -/
def integrateChecked (t : Tower n) (f : Term n) : Option (Result n) :=
  if admissible t && f.defined then some (integrate t f) else none

end SympyProofs.Calculus.Risch
