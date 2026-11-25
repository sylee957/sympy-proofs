module

public import SympyProofs.Calculus.Risch.Spec.Derivation
public import SympyProofs.Calculus.Risch.Spec.Linear

/-! What it means to solve the parametric equation `y′ + f y = Σ cᵢ gᵢ` in the field of a
tower: the result is a list of field elements and a linear system over the rationals, and
the solutions `(y, c)`, with `y` in the field and constants `cᵢ`, are exactly the
`y = Σ dⱼ hⱼ` for which `(c, d)` solves the system. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Linear

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

/-- The specification of part (b) of the Main Theorem for a program `slv`. -/
def SolveSpec (t : Tower n)
    (slv : Term n → List (Term n) → List (Term n) × List (List ℚ)) : Prop :=
  ∀ (f : Term n) (gs : List (Term n)), Term.InDomain k f → (∀ g ∈ gs, Term.InDomain k g) →
    (∀ h ∈ (slv f gs).1, Term.InDomain k h) ∧
    ∀ (y : K k n) (c : List k), c.length = gs.length →
      (t.der k y + Term.value k f * y = linComb c gs ↔
        ∃ d : List k, d.length = (slv f gs).1.length ∧ y = linComb d (slv f gs).1 ∧
          ∀ row ∈ (slv f gs).2, dotK row (c ++ d) = 0)

end SympyProofs.Calculus.Risch
