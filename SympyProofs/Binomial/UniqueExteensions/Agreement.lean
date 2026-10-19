module

public import SympyProofs.Binomial.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Integer agreement for the circle-integral extension

`AgreesWithSympyIntegers` specifies agreement with `choose` at every integer pair,
including negative arguments. It is the integer-data condition used by the
circle-integral characterization and its centered sampling variant.
-/

@[expose] public section

namespace SympyBinomial

/-- Agreement with SymPy's exact convention on the whole integer lattice. -/
abbrev AgreesWithSympyIntegers (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ n k : ℤ, F (n : ℂ) (k : ℂ) = ((choose n k : ℤ) : ℂ)

end SympyBinomial
