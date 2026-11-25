module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! The rows of a linear system computed by the programs have rational entries, and the
unknowns range over the constant field `k`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Linear

variable {k : Type} [Field k] [CharZero k]

/-- A rational row applied to a vector over `k`. -/
def dotK (row : List ℚ) (x : List k) : k :=
  (List.zipWith (fun (r : ℚ) (c : k) => (r : k) * c) row x).sum

end SympyProofs.Calculus.Risch.Linear
