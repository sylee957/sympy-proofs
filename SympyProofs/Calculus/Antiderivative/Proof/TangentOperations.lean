module

public import SympyProofs.Calculus.Antiderivative.Program.Operations
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Reference

/-! The recursion on native generators implements the proved exponential change of coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable [NatBound (K S 0)] [IntegerRelations (K S 0)] [ConstantFactors (K S 0)]

private theorem recursion_eq (c : K R 0 → K S 0) (i : K S 0) (t : Tower R n) :
    recursion c i t =
      let u := t.compile c i
      ⟨u.value, u.tower.gens, u.tower.level u.tangentFree,
        ⟨fun _ => u.tower.checkSteps u.tangentFree⟩⟩ := by
  induction t with
  | base => rfl
  | step t g ih =>
    cases g <;> simp only [recursion, ih] <;> rfl

/-- The decisions computed along the native generators agree with the decisions expressed
through the exponential tower used in the change-of-coordinates proof. -/
theorem Tower.tangentOperations_eq (t : Tower R n) (c : K R 0 → K S 0) (i : K S 0)
    (answer : Result S n → Result R n)
    (solutions : ℕ → List (K S n) × List (List (K S 0)) → List (K R n) × List (List (K R 0))) :
    t.tangentOperations c i answer solutions =
      (Operations.ofLevel (t.compile c i).tower (t.compile c i).tangentFree).inCoordinates
        (t.compile c i).value answer solutions := by
  unfold tangentOperations
  rw [recursion_eq]
  rfl

end SympyProofs.Calculus.Antiderivative
