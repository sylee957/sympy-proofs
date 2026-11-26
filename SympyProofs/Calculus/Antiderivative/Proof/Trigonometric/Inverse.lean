module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Reference
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Compiler

/-! The inverse substitutions in the extended coefficient field undo the forward compiler. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

/-- Retain the kinds of all generators over a new coefficient field. Their arguments have
no effect on rational substitution. -/
def Tower.shape (S : Type) [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S]
    [Div S] : {m : ℕ} → Tower R m → Tower S m
  | _, .base => .base
  | _, .step t g => (t.shape S).step (match g with
    | .prim _ => .prim 0
    | .exp _ => .exp 0
    | .tan _ => .tan 0)

variable [CharZero S]

/-- The forward rational substitution on arbitrary coefficients of the extended field. -/
noncomputable def Tower.forward (t : Tower R n) (i : K S 0) (hi : i^2 = -1) :
    K S n →+* K S n := (t.shape S).compileHom (RingHom.id _) i hi

private theorem forward_lift (t : Tower R n) (g : Gen (K R n)) (i : K S 0) (hi : i^2 = -1)
    (x : K S n) : (t.step g).forward i hi (K.lift x) = K.lift (t.forward i hi x) := by
  cases g <;> exact substituteHom_lift ..

private theorem forward_const (t : Tower R n) (i : K S 0) (hi : i^2 = -1) (c : K S 0) :
    t.forward i hi (K.ofConst c) = K.ofConst c := by
  induction t with
  | base => rfl
  | step t g ih => rw [← lift_ofConst, forward_lift, ih]

/-- The recovered exponential is transcendental over the lower coefficient field. -/
theorem Trigonometric.inverse_trans (i : K S 0) (hi : i^2 = -1) :
    Transcendental (M S n) (presentation S n (Kind.Tan.exponential i K.gen)) := by
  let a := K.equiv (K.ofConst i : K S n)
  have an : a ≠ 0 := by
    apply (map_ne_zero_iff _ K.equiv.injective).mpr
    apply (map_ne_zero_iff (K.ofConst (R := S) (n := n)) (RingHom.injective _)).mpr
    rintro rfl
    simp at hi
  let f := rationalMap (RingHom.id (M S n)) _ (tangent_transcendental an)
  have h : f (presentation S n (Kind.Tan.exponential i K.gen)) = RatFunc.X := by
    rw [Kind.Tan.exponential, ← lift_ofConst]
    simpa only [map_div₀, map_add, map_sub, presentation_gen, presentation_lift,
      f, rationalMap_C, rationalMap_X, RingHom.id_apply] using tangent_inverse an
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  rw [hc, show f (RatFunc.C c) = RatFunc.C c from rationalMap_C ..] at h
  apply RatFunc.transcendental_X (K := M S n)
  rw [← h, ← RatFunc.algebraMap_eq_C]
  exact isAlgebraic_algebraMap _

/-- The field homomorphism represented by the executable inverse substitutions. -/
noncomputable def Tower.restoreHom (i : K S 0) (hi : i^2 = -1) :
    {m : ℕ} → Tower R m → K S m →+* K S m
  | _, .base => RingHom.id _
  | _, .step t g =>
    match g with
    | .prim _ | .exp _ => substituteHom (t.restoreHom i hi) K.gen
      (by rw [presentation_gen]; exact RatFunc.transcendental_X)
    | .tan _ => substituteHom (t.restoreHom i hi) (Kind.Tan.exponential i K.gen)
      (inverse_trans i hi)

/-- The inverse field homomorphism is the function computed by recursive substitution. -/
theorem Tower.restoreHom_apply (t : Tower R n) (i : K S 0) (hi : i^2 = -1) (x : K S n) :
    t.restoreHom i hi x = t.restore i x := by
  induction t with
  | base => rfl
  | step t g ih =>
    have h := funext ih
    cases g <;> simp only [restoreHom, restore, substituteHom_apply, h]

/-- Recompilation after restoring any rational function recovers the original result. -/
theorem Tower.forward_restore (t : Tower R n) (i : K S 0) (hi : i^2 = -1) (x : K S n) :
    t.forward i hi (t.restore i x) = x := by
  rw [← t.restoreHom_apply i hi x]
  induction t with
  | base => rfl
  | step t g ih =>
    let f := (t.step g).forward i hi
    let h := (t.step g).restoreHom i hi
    apply step_induction x (fun w => f (h w) = w)
    · intro w
      have hw : h (K.lift w) = K.lift (t.restoreHom i hi w) := by
        cases g <;> exact substituteHom_lift ..
      rw [hw, forward_lift, ih]
    · cases g with
      | prim _ => simp [h, f, forward, shape, restoreHom, compileHom]
      | exp _ => simp [h, f, forward, shape, restoreHom, compileHom]
      | tan u =>
        have ht : h K.gen = Kind.Tan.exponential i K.gen := substituteHom_gen ..
        have hf : f K.gen = Kind.Tan.generator i := substituteHom_gen ..
        rw [ht, Kind.Tan.exponential, map_div₀, map_sub, map_add, hf,
          show f (K.ofConst i) = K.ofConst i from forward_const ..]
        exact Kind.Tan.exponential_generator i hi
    · intro _ _ ha hb; simp only [map_add, ha, hb]
    · intro _ _ ha hb; simp only [map_mul, ha, hb]
    · intro _ _ ha hb; simp only [map_div₀, ha, hb]

/-- The reverse round trip fixes every rational function in original generator coordinates. -/
theorem Tower.restore_forward (t : Tower R n) (i : K S 0) (hi : i^2 = -1) (x : K S n) :
    t.restore i (t.forward i hi x) = x :=
  (t.forward i hi).injective (t.forward_restore i hi _)

end SympyProofs.Calculus.Antiderivative
