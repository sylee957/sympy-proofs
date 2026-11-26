module

public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite

/-! Implicit differentiation of the residue at an algebraic root of a normal denominator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

variable {F : Type} [Field F] [DecidableEq F]

/-- The derivative of a separable root, represented modulo its defining polynomial. -/
def rootVelocity (D : F → F) (s : Poly F) : Poly F :=
  -(s.map D) * (bezout s.derivative s).1 % s

/-- Numerators of the derivatives of the residues, reduced modulo their common denominator. -/
def residueDerivatives (D : F → F) (dx s : Poly F) (as : List (Poly F)) : List (Poly F) :=
  let inverse := (bezout (polyDer D dx s) s).1
  let rootD := rootVelocity D s
  (as.map fun a => a * inverse % s).map fun h => polyDer D rootD h % s

end SympyProofs.Calculus.Antiderivative.Step
