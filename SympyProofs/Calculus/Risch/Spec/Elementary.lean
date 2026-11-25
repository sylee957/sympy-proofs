module

public import SympyProofs.Calculus.Risch.Spec.Derivation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! An element of the field of a tower has an elementary integral over that field when it is
the derivative of an element of the field plus a combination, with constant coefficients, of
logarithmic derivatives of elements of the field. By Liouville's theorem this is the form of
every integral in an elementary extension. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

/-- `f = v′ + Σ cᵢ uᵢ′ / uᵢ` with `v`, `uᵢ` in the field and constants `cᵢ`. -/
def Tower.Elementary (t : Tower n) (f : K k n) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → k) (u : ι → K k n) (v : K k n),
    f = t.der k v + ∑ i, constHom k n (c i) * (t.der k (u i) / u i)

end SympyProofs.Calculus.Risch
