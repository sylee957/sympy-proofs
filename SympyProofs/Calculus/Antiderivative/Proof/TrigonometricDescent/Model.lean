module

public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Coordinates
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.ConstantModel

/-! Interpretation of both quadratic coordinates under either choice of the imaginary unit. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))]
local notation "E" => WithI (K R 0)
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]
variable [Algebra (WithI (K R 0)) k] [FaithfulSMul (WithI (K R 0)) k]
variable (hc : ∀ a : K R 0, Model.constantHom k (quadraticConstantHom a) = Model.constantHom k a)

include hc

/-- Extending the coefficient field preserves the value of every original rational function. -/
theorem val_extendGround (n : ℕ) (z : K R n) : val k (extendGround n z) = val k z := by
  induction n with
  | zero =>
    change val k (quadraticConstantHom z) = val k z
    rw [← Model.C_zero_constantHom, ← Model.C_zero_constantHom, hc]
  | succ n ih =>
    let h := (val k).comp (extendGroundHom (R := R) (n+1))
    rw [← extendGroundHom_apply]
    change h z = val k z
    apply step_induction z (fun a => h a = val k a)
    · intro a
      change val k (extendGroundHom (n+1) (K.lift a)) = val k (K.lift a)
      simp [ih]
    · change val k (extendGroundHom (R := R) (n+1) K.gen) = val k (K.gen : K R (n+1))
      simp
    · intro a b ha hb; rw [map_add, map_add, ha, hb]
    · intro a b ha hb; rw [map_mul, map_mul, ha, hb]
    · intro a b ha hb; rw [map_div₀, map_div₀, ha, hb]

/-- In the model the original function is its real coordinate plus j times its imaginary
coordinate. This holds for both embeddings of the quadratic constants. -/
theorem val_project (j : k)
    (hi : Model.constantHom k (K.C (WithI.imaginary (K R 0)) : K (WithI (K R 0)) 0) = j)
    (n : ℕ) (x : K E n) :
    val k x = val k (project n x).re + Model.C k n j * val k (project n x).im := by
  have im : val k (K.C (WithI.imaginary (K R 0)) : K E n) = Model.C k n j := by
    rw [modelConstant_C (R := E) k (WithI.imaginary (K R 0))] at hi
    simp [val, Model.C, ← hi]
  calc
    val k x = val k (assemble n (project n x)) := congrArg (val k) (assemble_project n x).symm
    _ = _ := by rw [assemble, map_add, map_mul, val_extendGround k hc, val_extendGround k hc, im]

/-- Scalar interpretation at height zero is the same pair formula in k. -/
theorem constantHom_project (j : k)
    (hi : Model.constantHom k (K.C (WithI.imaginary (K R 0)) : K (WithI (K R 0)) 0) = j)
    (x : K E 0) :
    Model.constantHom k x = Model.constantHom k (project 0 x).re +
      j * Model.constantHom k (project 0 x).im := by
  apply (Model.C k 0).injective
  simp only [map_add, map_mul, Model.C_zero_constantHom]
  exact val_project k hc j hi 0 x

end SympyProofs.Calculus.Antiderivative.Trigonometric
