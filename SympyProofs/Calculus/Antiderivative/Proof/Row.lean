module

public import SympyProofs.Calculus.Antiderivative.Spec.Level
public import SympyProofs.Calculus.Antiderivative.Proof.Linear

/-! Convert homogeneous model rows to linear equations in the constants themselves. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Model

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- Casting the value of a constant row into the zero-height model gives the model combination. -/
theorem C_functional (row : List (K R 0)) (c : List k) :
    C k 0 (Linear.functional (constantHom k) c.length row (Linear.vector (RingHom.id k) _ c)) =
      linearCombination k c row := by
  induction c generalizing row with
  | nil => simp [linearCombination]
  | cons x xs ih =>
    cases row with
    | nil => simp [linearCombination]
    | cons y ys =>
      have h := ih ys
      simp only [Linear.functional_apply, Linear.vector] at h
      simp [linearCombination, Fin.sum_univ_succ, Linear.vector, C_zero_constantHom,
        mul_comm] at h ⊢
      exact h

/-- The model row holds exactly when the homogeneous linear functional vanishes. -/
theorem rowHolds_iff_functional (row : List (K R 0)) (c : List k) :
    rowHolds k row c ↔
      Linear.functional (constantHom k) c.length row (Linear.vector (RingHom.id k) _ c) = 0 := by
  rw [rowHolds, ← C_functional k]
  exact map_eq_zero_iff _ (C k 0).injective

end SympyProofs.Calculus.Antiderivative.Model
