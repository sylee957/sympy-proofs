module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Compiler
public import SympyProofs.Calculus.Antiderivative.Proof.Coefficients
public import SympyProofs.Calculus.Antiderivative.Spec.Integration

/-! Over a model containing the chosen imaginary unit, the compiler changes coordinates by a
differential-field isomorphism. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k]

/-- Extend the model coordinate isomorphism by a new transcendental rational coordinate. -/
noncomputable def Trigonometric.changeStep (h : M k n ≃+* M k n) (z : RatFunc (M k n))
    (hz : Transcendental (M k n) z) (hs : Function.Surjective (rationalMap h.toRingHom z hz)) :
    M k (n+1) ≃+* M k (n+1) :=
  (Model.stepEquiv k n).trans ((RingEquiv.ofBijective (rationalMap h.toRingHom z hz)
    ⟨RingHom.injective _,hs⟩).trans (Model.stepEquiv k n).symm)

omit [CharZero k] in
theorem Trigonometric.x_surjective (h : M k n ≃+* M k n) :
    Function.Surjective (rationalMap h.toRingHom RatFunc.X RatFunc.transcendental_X) := by
  apply rationalMap_surjective _ _ _ h.surjective
  exact ⟨RatFunc.X,rationalMap_X ..⟩

/-- The mixed coordinate change acts on the model field, fixing all model constants. -/
noncomputable def Tower.changeModel (j : k) (hj : j ≠ 0) :
    {m : ℕ} → Tower R m → M k m ≃+* M k m
  | _, .base => RingEquiv.refl _
  | m+1, .step t g =>
    let h := changeModel j hj t
    match g with
    | .prim _ | .exp _ => changeStep k h RatFunc.X RatFunc.transcendental_X (x_surjective k h)
    | .tan _ =>
      let c := Model.C k m j
      let hc := (map_ne_zero_iff _ (Model.C k m).injective).mpr hj
      changeStep k h (tangentValue c) (tangent_transcendental hc)
        (rationalMap_tangent_surjective _ h.surjective c hc)

omit [CharZero k] in
private theorem changeStep_lift (h : M k n ≃+* M k n) (z : RatFunc (M k n)) (hz hs) (x : M k n) :
    changeStep k h z hz hs (Model.includeVars (Nat.le_succ n) x) =
      Model.includeVars (Nat.le_succ n) (h x) := by
  apply (Model.stepEquiv k n).injective
  simp [changeStep, Model.stepEquiv_includeVars]

omit [CharZero k] in
private theorem changeStep_last (h : M k n ≃+* M k n) (z : RatFunc (M k n)) (hz hs) :
    Model.stepEquiv k n (changeStep k h z hz hs
      (Model.polynomial k (MvPolynomial.X (Fin.last n)))) = z := by
    simp [changeStep, Model.polynomial]

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem Tower.changeModel_lift (t : Tower R n) (g : Gen (K R n)) (j : k) (hj : j ≠ 0)
    (x : M k n) : (t.step g).changeModel k j hj (Model.includeVars (Nat.le_succ n) x) =
      Model.includeVars (Nat.le_succ n) (t.changeModel k j hj x) := by
  cases g <;> simp only [changeModel, changeStep_lift]

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
@[simp] theorem Tower.changeModel_C (t : Tower R n) (j : k) (hj : j ≠ 0) (c : k) :
    t.changeModel k j hj (Model.C k n c) = Model.C k n c := by
  induction t with
  | base => rfl
  | @step n t g ih =>
    rw [← Model.includeVars_C k (Nat.le_succ n) c, changeModel_lift, ih]

variable [Algebra R k] [FaithfulSMul R k] [Algebra S k] [FaithfulSMul S k]

omit [CharZero k] in
private theorem stepEquiv_tangent (i : K S 0) : Model.stepEquiv k n (val k (Kind.Tan.generator i)) =
    tangentValue (Model.C k n (Model.constantHom k i)) := by
  simp only [Kind.Tan.generator, tangentValue, map_div₀, map_mul, map_neg, map_sub, map_add,
    map_one, val_gen, Model.stepEquiv_last, ← Model.C_constantHom, Model.stepEquiv_scalar]

omit [CharZero k] in
theorem Trigonometric.constant_ne (i : K S 0) (hi : i^2 = -1) : Model.constantHom k i ≠ 0 := by
  rw [map_ne_zero_iff _ (Model.constantHom (R := S) k).injective]
  rintro rfl
  simp at hi

variable [CharZero S]

/-- Evaluating an original rational input in the changed model coordinates gives exactly the
value produced by compilation. -/
theorem Tower.changeModel_val (c : K R 0 →+* K S 0)
    (hc : ∀ a, Model.constantHom k (c a) = Model.constantHom k a) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (x : K R n) : t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
      (val k x) = val k (t.compileHom c i hi x) := by
  let j := Model.constantHom k i
  let hj := constant_ne k i hi
  induction t with
  | base =>
    change val k x = val k (c x)
    rw [← Model.C_zero_constantHom, ← Model.C_zero_constantHom, hc]
  | @step n t g ih =>
    let h := (t.step g).changeModel k j hj
    let f := (t.step g).compileHom c i hi
    apply step_induction x (fun x => h (val k x) = val k (f x))
    · intro a
      have hf : f (K.lift a) = K.lift (t.compileHom c i hi a) := by
        cases g <;> exact substituteHom_lift ..
      rw [hf, val_lift, val_lift]
      exact (Tower.changeModel_lift ..).trans (congrArg _ (ih a))
    · apply (Model.stepEquiv k n).injective
      rw [Antiderivative.val_gen]
      cases g with
      | prim b => simp only [h, f, Tower.changeModel, Tower.compileHom, substituteHom_gen,
          Antiderivative.val_gen, Model.stepEquiv_last, changeStep_last]
      | exp a => simp only [h, f, Tower.changeModel, Tower.compileHom, substituteHom_gen,
          Antiderivative.val_gen, Model.stepEquiv_last, changeStep_last]
      | tan a =>
        rw [show f K.gen = Kind.Tan.generator i from substituteHom_gen .., stepEquiv_tangent]
        simp only [h, Tower.changeModel, changeStep_last, j]
    · intro a b ha hb; simp only [map_add, ha, hb]
    · intro a b ha hb; simp only [map_mul, ha, hb]
    · intro a b ha hb; simp only [map_div₀, ha, hb]

/-- The coordinate isomorphism transports all model derivatives, also on elements with
coefficients in the extended model constant field. -/
theorem Tower.changeModel_D (c : K R 0 →+* K S 0)
    (hc : ∀ a, Model.constantHom k (c a) = Model.constantHom k a) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (x : M k n) :
    let e := t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
    e (t.modelD k x) = (t.compile c i).tower.modelD k (e x) := by
  let e := t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
  let u := (t.compile c i).tower
  have h (z : K R n) : e (val k z) = val k (t.compileHom c i hi z) :=
    t.changeModel_val k c hc i hi z
  change e (t.modelD k x) = u.modelD k (e x)
  symm
  apply Model.map_derivation k e.toRingHom _ (u.modelD k)
  · intro a
    change u.modelD k (e (Model.C k n a)) = 0
    rw [show e (Model.C k n a) = _ from t.changeModel_C k _ _ a]
    exact u.modelD_C k a
  · intro m
    let z := K.ofPoly (MPoly.X m : MPoly n R)
    have hv : val k z = Model.polynomial k (MvPolynomial.X m) := by simp [z, Model.polynomial]
    change u.modelD k (e (Model.polynomial k (MvPolynomial.X m))) = _
    rw [← hv, h, ← Tower.val_D, ← t.compileHom_D c i hi, ← h,
      Tower.val_D, hv]
    change e (Model.derivation k _ _) = _
    rw [Model.derivation_X]
    rfl

/-- The coordinate isomorphism preserves the kernel of the derivation and fixes constants. -/
theorem Tower.compile_admissible_iff (c : K R 0 →+* K S 0)
    (hc : ∀ a, Model.constantHom k (c a) = Model.constantHom k a) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) : (t.compile c i).tower.Admissible k ↔ t.Admissible k := by
  let e := t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
  let u := (t.compile c i).tower
  have kernel (x : M k n) : u.modelD k (e x) = 0 ↔ t.modelD k x = 0 := by
    rw [← show e (t.modelD k x) = _ from t.changeModel_D k c hc i hi x]
    exact map_eq_zero_iff _ e.injective
  have constant (x : M k n) : (∃ a, e x = Model.C k n a) ↔ ∃ a, x = Model.C k n a := by
    apply exists_congr
    intro a
    exact (congrArg (e x = ·) (t.changeModel_C k _ _ a).symm).to_iff.trans e.injective.eq_iff
  constructor
  · intro h x
    exact (kernel x).symm.trans ((h (e x)).trans (constant x))
  · intro h y
    obtain ⟨x,rfl⟩ := e.surjective y
    exact (kernel x).trans ((h x).trans (constant x).symm)

end SympyProofs.Calculus.Antiderivative
