module

public import SympyProofs.Calculus.Antiderivative.Program.Level
public import SympyProofs.Calculus.Antiderivative.Program.Linear

/-! Reading an exponential admissibility decision and an integer exponent from rational rows. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Test whether every rational row vanishes on the given coefficient vector. -/
def satisfiesRows (q : List ℚ) (rows : List (List ℚ)) : Bool :=
  rows.all fun r => Linear.dot q r == 0

/-- The first row involving the second coordinate determines the only possible exponent.
A nonnegative integral slope gives that exponent exactly. -/
def exponentBound (rows : List (List ℚ)) : ℕ :=
  match rows.find? (fun r => r.getD 1 0 != 0) with
  | none => 0
  | some row => Rational.natBound (-(row.getD 0 0) / row.getD 1 0)

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Test whether the new exponential preserves the constant field, using its lower-level rows. -/
def Level.expOk {n : ℕ} (L : Level R n) (D : K R n → K R n) (u : K R n) : Bool :=
  !(satisfiesRows [1] (L.logRelations [D u]))

end SympyProofs.Calculus.Antiderivative
