module

public import SympyProofs.Calculus.Antiderivative.Spec.Level

/-! Admissibility as preservation of the coefficient field of constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The functions killed by the tower derivative are exactly the coefficient-model constants. -/
def Tower.Admissible (t : Tower R n) : Prop :=
  ∀ x, t.modelD k x = 0 ↔ ∃ a, x = Model.C k n a

end SympyProofs.Calculus.Antiderivative
