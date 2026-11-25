module

public import SympyProofs.Calculus.Risch.Program.Poly

/-! The derivative of a polynomial in the newest generator `θ`. With `θ′ = a θ + b`, where
`a = u′` and `b = 0` at an exponential step and `a = 0` at a primitive step, the coefficient
of `θⁱ` in `P′` is `pᵢ′ + i a pᵢ + (i + 1) b pᵢ₊₁`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Tower

/-- The tower below the newest generator. -/
def parent : Tower (n + 1) → Tower n
  | .prim t _ | .exp t _ => t

/-- The logarithmic derivative of an exponential generator: `u′`, and zero at a primitive
step. -/
def twist : Tower (n + 1) → Term n
  | .prim _ _ => .const 0
  | .exp t u => t.D u

/-- The derivative of a primitive generator: `b`, and zero at an exponential step. -/
def shift : Tower (n + 1) → Term n
  | .prim _ b => b
  | .exp _ _ => .const 0

end Tower

namespace Poly

/-- The derivative of a polynomial in the newest generator. -/
def der (t : Tower (n + 1)) (p : Poly n) : Poly n :=
  (List.range p.length).map fun i =>
    Coeff.add (t.parent.D (coeff p i))
      (Coeff.add (Coeff.mul (Coeff.mul (.const (i : Rat)) t.twist) (coeff p i))
        (Coeff.mul (Coeff.mul (.const ((i + 1 : Nat) : Rat)) t.shift) (coeff p (i + 1))))

end Poly

end SympyProofs.Calculus.Risch
