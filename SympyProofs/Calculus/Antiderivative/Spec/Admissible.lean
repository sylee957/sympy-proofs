module

public import SympyProofs.Calculus.Antiderivative.Spec.Integration

/-! Conditions for a primitive or exponential generator to preserve the constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- A primitive has no antiderivative below. For an exponential, no positive integral multiple
of its logarithmic velocity is the logarithmic derivative of a nonzero element below. -/
def ReducedGen.Admissible (t : Tower R n) : ReducedGen (K R n) → Prop
  | .prim b => ¬ ∃ y : M k n, t.modelD k y = val k b
  | .exp u => ¬ ∃ (m : ℕ) (y : M k n), 0 < m ∧ y ≠ 0 ∧
      t.modelD k y / y = (m : M k n) * val k (t.D u)

end SympyProofs.Calculus.Antiderivative
