module

public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Program.Linear

/-! Recover a particular field solution from the lower level's homogeneous constraints. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Combine field elements with constant coefficients, ignoring unmatched trailing entries. -/
def Level.combine (cs : List (K R 0)) (hs : List (K R n)) : K R n :=
  (List.zipWith (fun c h => K.ofConst c * h) cs hs).sum

/-- A field solution of `y′ + f y = g`, if one exists. -/
def Level.rde (lower : Level R n) (f g : K R n) : Option (K R n) := do
  let (hs, rows) := lower.solve f [g]
  let v ← Linear.normalized rows (hs.length + 1)
  return Level.combine v.tail hs

/-- A constant `c` and field element `y` such that `y′ = g - c b`, if they exist. -/
def Level.limited (lower : Level R n) (g b : K R n) : Option (K R 0 × K R n) := do
  let (hs, rows) := lower.solve 0 [g,b]
  let v ← Linear.normalized rows (hs.length + 2)
  return (-v.getD 1 0, Level.combine (v.drop 2) hs)

end SympyProofs.Calculus.Antiderivative
