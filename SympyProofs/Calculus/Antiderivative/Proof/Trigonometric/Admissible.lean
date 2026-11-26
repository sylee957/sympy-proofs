module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Reference
public import SympyProofs.Calculus.Antiderivative.Proof.DecisionLevel
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.ConstantModel
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Model

/-! The mixed-tower acceptance test decides preservation of the original model constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

section Existing

variable [IsAlgClosed k] [CharZero S] [Algebra S k] [FaithfulSMul S k]
variable [NatBound (K S 0)] [LawfulNatBound (K S 0)]
variable [IntegerRelations (K S 0)] [LawfulIntegerRelations (K S 0)]
variable [ConstantFactors (K S 0)] [LawfulConstantFactors (K S 0)]

/-- The original-coordinate test accepts exactly when the native tower has no new constants. -/
theorem Tower.admissibleOriginal_iff (t : Tower R n) (c : K R 0 →+* K S 0)
    (hc : ∀ x, Model.constantHom k (c x) = Model.constantHom k x) (i : K S 0) (hi : i^2 = -1) :
    t.admissibleOriginal c i = true ↔ t.Admissible k :=
  let u := t.compile c i
  (u.tower.checkSteps_iff k u.tangentFree).trans (t.compile_admissible_iff k c hc i hi)

end Existing

variable [IsAlgClosed k] [Fact (¬ IsSquare (-1 : K R 0))]
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]
variable [IntegerRelations (K R 0)] [LawfulIntegerRelations (K R 0)]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]

/-- The test that automatically adjoins an imaginary unit accepts exactly the mixed towers
whose original model constant field is preserved. -/
theorem Tower.admissibleAdjoinI_iff (t : Tower R n) :
    t.admissibleAdjoinI = true ↔ t.Admissible k := by
  obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) zero_lt_two
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  let _ : CharZero (K R 0) := (Model.constantHom (R := R) k).charZero
  let _ : CharZero (WithI (K R 0)) := (quadraticModelHom (R := R) k j hj).charZero
  exact t.admissibleOriginal_iff k quadraticConstantHom (quadraticConstantHom_compatible k j hj)
    (K.C (WithI.imaginary (K R 0))) quadraticI_sq

end SympyProofs.Calculus.Antiderivative
