module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Python.Math

/-- Python's `math.prod` on nonnegative integer sequences, with its default start of one. -/
def prod (values : Array ℕ) : ℕ :=
  values.foldl (· * ·) 1

/-- The left-to-right multiplication computes the mathematical product. -/
theorem prod_eq_prod (values : Array ℕ) : prod values = values.toList.prod := by
  rw [prod, ← Array.prod_eq_foldl_nat, Array.prod_toList]

end Python.Math
