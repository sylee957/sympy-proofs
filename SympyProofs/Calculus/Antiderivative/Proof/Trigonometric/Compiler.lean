module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Coordinates

/-! The mixed tower compiler is an embedding of differential fields in its original coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

theorem Trigonometric.lift_ofConst (c : K S 0) :
    K.lift (K.ofConst c : K S n) = K.ofConst (n := n+1) c := by
  apply (val (FractionRing S)).injective
  simp only [val_lift, ← Model.C_constantHom, Model.includeVars_C]

theorem Trigonometric.presentation_tangent (i : K S 0) :
    presentation S n (Kind.Tan.generator i) = tangentValue (K.equiv (K.ofConst i : K S n)) := by
  rw [Kind.Tan.generator, ← lift_ofConst]
  simp [tangentValue]
  rw [← K.equiv_lift, K.stepEquiv_lift]

variable [CharZero S]

private theorem sqrt_ne_zero (i : K S 0) (hi : i ^ 2 = -1) : i ≠ 0 := by rintro rfl; simp at hi

theorem Trigonometric.tan_coordinate_transcendental (i : K S 0) (hi : i ^ 2 = -1) :
    Transcendental (M S n) (presentation S n (Kind.Tan.generator i)) := by
  rw [presentation_tangent]
  exact tangent_transcendental ((map_ne_zero_iff _ K.equiv.injective).mpr
    ((map_ne_zero_iff _ K.ofConst.injective).mpr (sqrt_ne_zero _ hi)))

omit [CharZero S] in
theorem Trigonometric.gen_coordinate_transcendental :
    Transcendental (M S n) (presentation S n K.gen) :=
  by rw [presentation_gen]; exact RatFunc.transcendental_X

/-- The bundled field homomorphism computed by a mixed tangent tower. -/
noncomputable def Tower.compileHom (constants : K R 0 →+* K S 0) (i : K S 0) (hi : i^2 = -1) :
    {m : ℕ} → Tower R m → K R m →+* K S m
  | _, .base => constants
  | _, .step t g =>
    match g with
    | .prim _ | .exp _ =>
      substituteHom (t.compileHom constants i hi) K.gen gen_coordinate_transcendental
    | .tan _ => substituteHom (t.compileHom constants i hi) (Kind.Tan.generator i)
      (tan_coordinate_transcendental i hi)

theorem Tower.compileHom_apply (constants : K R 0 →+* K S 0) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (x : K R n) :
    t.compileHom constants i hi x = (t.compile constants i).value x := by
  induction t with
  | base => rfl
  | step t g ih =>
    have eqf := funext ih
    cases g <;> simp only [compileHom, compile, substituteHom_apply, eqf]

/-- Every compiled rational substitution is injective. -/
theorem Tower.compile_injective (constants : K R 0 →+* K S 0) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) : Function.Injective (t.compile constants i).value := by
  rw [← funext (t.compileHom_apply constants i hi)]
  exact (t.compileHom constants i hi).injective

omit [CharZero S] in
private theorem step_deriv {t : Tower R n} (g : Gen (K R n)) (lower : K R n →+* K S n)
    (u : Tower S n) (v : Gen (K S n))
    (f : K R (n+1) →+* K S (n+1))
    (hl : ∀ a, f (K.lift a) = K.lift (lower a)) (hi : ∀ a, lower (t.D a) = u.D (lower a))
    (hg : f ((t.step g).D K.gen) = (u.step v).D (f K.gen)) (x : K R (n+1)) :
    f ((t.step g).D x) = (u.step v).D (f x) := by
  apply step_induction x (fun x => f ((t.step g).D x) = (u.step v).D (f x))
  · intro a
    rw [Tower.D_lift, hl, hl, Tower.D_lift, hi]
  · exact hg
  · intro a b ha hb
    change f (K.derivation _ (a+b)) = K.derivation _ (f (a+b))
    simp only [map_add, K.derivation_apply]
    exact congrArg₂ (· + ·) ha hb
  · intro a b ha hb
    change f (K.derivation _ (a*b)) = K.derivation _ (f (a*b))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
    change _ * f ((t.step g).D b) + _ * f ((t.step g).D a) = _
    rw [ha, hb]
    rfl
  · intro a b ha hb
    change f (K.derivation _ (a/b)) = K.derivation _ (f (a/b))
    simp only [map_div₀, Derivation.leibniz_div, smul_eq_mul, map_mul, map_sub,
      map_pow, map_inv₀]
    change _ * (_ * f ((t.step g).D a) - _ * f ((t.step g).D b)) = _
    rw [ha, hb]
    rfl

/-- The compiler preserves the native derivative of every mixed rational input. -/
theorem Tower.compileHom_D (constants : K R 0 →+* K S 0) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (x : K R n) : t.compileHom constants i hi (t.D x) =
      (t.compile constants i).tower.D (t.compileHom constants i hi x) := by
  induction t with
  | base =>
    change constants (K.der [] x) = K.der [] (constants x)
    simp [K.der_eq_weightedPartials, K.weightedPartials]
  | step t g ih =>
    let f := t.compileHom constants i hi
    let u := (t.compile constants i).tower
    have he (x) : f x = (t.compile constants i).value x := t.compileHom_apply constants i hi x
    have hD (x) : f (t.D x) = u.D (f x) := ih x
    cases g with
    | prim b =>
      simp only [compile, ← he, compileHom]
      apply step_deriv (.prim b) f u (.prim (f b)) _ (substituteHom_lift _ _ _) ih
      simp only [Tower.D_gen_prim, substituteHom_gen, substituteHom_lift,
        Tower.D_gen_prim]
    | exp a =>
      simp only [compile, ← he, compileHom]
      apply step_deriv (.exp a) f u (.exp (f a)) _ (substituteHom_lift _ _ _) ih
      simp only [Tower.D_gen_exp, substituteHom_gen, substituteHom_lift, map_mul,
        Tower.D_gen_exp, hD]
    | tan a =>
      simp only [compile, ← he, compileHom]
      apply step_deriv (.tan a) f u (.exp (2 * K.ofConst i * f a)) _ (substituteHom_lift _ _ _) ih
      simp only [Tower.D_gen_tan, map_mul, map_add, map_one, map_pow,
        substituteHom_lift, substituteHom_gen, hD]
      exact (Kind.Tan.generator_deriv u i hi (f a)).symm

theorem Tower.compile_D (constants : K R 0 →+* K S 0) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (x : K R n) : (t.compile constants i).value (t.D x) =
      (t.compile constants i).tower.D ((t.compile constants i).value x) := by
  simpa only [t.compileHom_apply] using t.compileHom_D constants i hi x

end SympyProofs.Calculus.Antiderivative
