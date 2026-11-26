module

public import SympyProofs.Calculus.Antiderivative.Program.Logarithmic
public import SympyProofs.Calculus.Antiderivative.Spec.Admissible
public import SympyProofs.Calculus.Antiderivative.Spec.IntegerRelations

/-! Rational combinations with logarithmic derivatives after clearing an integer multiple. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- A positive integer multiple of the given field element is a logarithmic derivative. -/
def Tower.SaturatedLog (t : Tower R n) (w : M k n) : Prop :=
  ∃ (m : ℕ) (y : M k n), 0 < m ∧ y ≠ 0 ∧ t.modelD k y / y = m * w

/-- Rational rows describe all logarithmic derivative relations up to an integer multiple. -/
def Level.LogRelationsSpec (t : Tower R n) (L : Level R n) : Prop :=
  ∀ (w : List (K R n)) (q : List ℚ), w.length = q.length →
    ((∀ r ∈ L.logRelations w, Linear.dot q r = 0) ↔
      t.SaturatedLog k (val k (rationalCombination q w)))

end SympyProofs.Calculus.Antiderivative
