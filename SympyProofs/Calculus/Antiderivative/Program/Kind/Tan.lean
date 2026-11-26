module

public import SympyProofs.Calculus.Antiderivative.Program.Tower

/-! Realizing a tangent generator by a single exponential over constants containing i. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Tan

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- The exponential tower containing the tangent of u, using a constant i with i² = −1. -/
def tower (t : Tower R n) (i : K R 0) (u : K R n) : Tower R (n + 1) :=
  t.step (.exp (2 * K.ofConst i * u))

/-- The tangent as a rational function of the new exponential generator. -/
def generator (i : K R 0) : K R (n + 1) :=
  -K.ofConst i * (K.gen - 1) / (K.gen + 1)

/-- Recover the exponential from the tangent by the inverse change of variable. -/
def exponential (i : K R 0) (z : K R (n + 1)) : K R (n + 1) :=
  (K.ofConst i - z) / (K.ofConst i + z)

end SympyProofs.Calculus.Antiderivative.Kind.Tan
