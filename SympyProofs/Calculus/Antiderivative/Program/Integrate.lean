module

public import SympyProofs.Calculus.Antiderivative.Program.Operations
public import SympyProofs.Calculus.Antiderivative.Program.Verify

/-! One-shot integration and parametric solving on native towers. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

variable [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]
variable [Decidable (IsSquare (-1 : K R 0))]

/-- Decide whether adjoining the generators preserves the constant field. -/
def Tower.admissible (t : Tower R n) : Bool := t.operations.admissible.get

/-- Integrate a field element of an admissible tower in its original coordinates. -/
def integrate (t : Tower R n) (f : K R n) : Result R n := t.operations.integrate f

/-- Solve the parametric differential equation on an admissible tower. -/
def solve (t : Tower R n) (f : K R n) (gs : List (K R n)) :
    List (K R n) × List (List (K R 0)) := t.operations.solve f gs

namespace Tower
export Antiderivative (integrate solve)
end Tower

end SympyProofs.Calculus.Antiderivative
