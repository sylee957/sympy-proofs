module

public import SympyProofs.Calculus.Antiderivative.Proof.StepModel
public import SympyProofs.Calculus.Antiderivative.Spec.Level

/-! Field terms and weighted root sums preserve their meanings under inclusion, scaling,
and addition of a field primitive. Every answer differentiates to a Liouville form. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

@[simp] theorem Tower.modelD_includeVars (t : Tower R n) (g : Gen (K R n))
    (x : M k n) :
    (t.step g).modelD k (Model.includeVars (Nat.le_succ n) x) =
      Model.includeVars (Nat.le_succ n) (t.modelD k x) := by
  apply (Model.stepEquiv k n).injective
  rw [Tower.stepEquiv_modelD, Model.stepEquiv_includeVars, Model.stepEquiv_includeVars,
    Model.extendVariable_C]

@[simp] theorem RootSum.argAt_lift (s : RootSum R n) (c : k) :
    s.lift.argAt k c = Model.includeVars (Nat.le_succ n) (s.argAt k c) := by
  rw [argAt, lift, Poly.equiv_map, Polynomial.eval₂_map, argAt, Polynomial.hom_eval₂]
  congr 1
  · ext x
    exact val_lift k x
  · exact (Model.includeVars_C k _ c).symm

@[simp] theorem RootSum.regular_lift (s : RootSum R n) : s.lift.Regular k ↔ s.Regular k := by
  simp only [Regular, argAt_lift, ne_eq, map_eq_zero]
  rfl

@[simp] theorem RootSum.deriv_lift (t : Tower R n) (g : Gen (K R n)) (s : RootSum R n) :
    s.lift.deriv k (t.step g) = Model.includeVars (Nat.le_succ n) (s.deriv k t) := by
  classical
  simp only [deriv, argAt_lift, Tower.modelD_includeVars, map_mul, map_sum, map_div₀,
    ← Model.C_constantHom, Model.includeVars_C]
  rfl

@[simp] theorem Answer.regular_lift (a : Answer R n) : a.lift.Regular k ↔ a.Regular k := by
  simp [Regular, lift, RootSum.regular_lift]

@[simp] theorem Answer.deriv_lift (t : Tower R n) (g : Gen (K R n)) (a : Answer R n) :
    a.lift.deriv k (t.step g) = Model.includeVars (Nat.le_succ n) (a.deriv k t) := by
  simp [deriv, lift, List.map_map, Function.comp_def, map_list_sum]

@[simp] theorem Answer.regular_addField (a : Answer R n) (y : K R n) :
    (a.addField y).Regular k ↔ a.Regular k := Iff.rfl

@[simp] theorem Answer.deriv_addField (t : Tower R n) (a : Answer R n) (y : K R n) :
    (a.addField y).deriv k t = a.deriv k t + t.modelD k (val k y) := by
  simp [deriv, addField, add_right_comm]

@[simp] theorem Answer.regular_scale (c : K R 0) (a : Answer R n) :
    (a.scale c).Regular k ↔ a.Regular k := by simp [scale, Regular, RootSum.Regular,
      RootSum.modelModulus, RootSum.argAt]

@[simp] theorem Answer.deriv_scale (t : Tower R n) (c : K R 0) (a : Answer R n) :
    (a.scale c).deriv k t = val k (K.ofConst c) * a.deriv k t := by
  have hc : t.modelD k (val k (K.ofConst c : K R n)) = 0 := by
    rw [← Model.C_constantHom]
    exact Model.derivation_C k _ _
  simp only [deriv, scale, map_mul, Derivation.leibniz, hc, smul_eq_mul, mul_zero, add_zero,
    List.map_map, mul_add, Function.comp_def]
  congr 1
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  simp [RootSum.deriv, mul_assoc, RootSum.argAt, RootSum.modelModulus]

/-- The formal derivative of every answer is a finite sum of logarithmic derivatives and
a field derivative. Each distinct constant root gives one logarithmic term. -/
theorem Answer.deriv_elementary (t : Tower R n) (a : Answer R n) :
    t.Elementary k (a.deriv k t) := by
  classical
  let term (s : k × M k n) := Model.C k n s.1 * (t.modelD k s.2 / s.2)
  have single (s : RootSum R n) :
      ∃ logs : List (k × M k n), s.deriv k t = (logs.map term).sum := by
    let Z := (s.modelModulus k).roots.toFinset
    refine ⟨Z.toList.map (fun c => (Model.constantHom k s.weight * c, s.argAt k c)), ?_⟩
    simp only [List.map_map, Finset.sum_map_toList, RootSum.deriv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Function.comp_apply, term, map_mul, ← Model.C_constantHom, mul_assoc]
  obtain ⟨logs, hlogs⟩ : ∃ logs : List (k × M k n),
      (a.sums.map (RootSum.deriv k t)).sum = (logs.map term).sum := by
    induction a.sums with
    | nil => exact ⟨[], rfl⟩
    | cons s ss ih =>
      obtain ⟨xs,hx⟩ := single s
      obtain ⟨ys,hy⟩ := ih
      exact ⟨xs ++ ys, by simp [hx, hy]⟩
  exact ⟨val k a.field, logs, congrArg (t.modelD k (val k a.field) + ·) hlogs⟩

/-- The integrator returns a regular answer exactly when its input has a primitive in the
answer language. A formal equality of derivatives already suffices for this direction. -/
theorem Tower.IntegrateSpec.iff_answer {t : Tower R n} {integral : K R n → Result R n}
    (hs : t.IntegrateSpec k integral) (f : K R n) :
    (∃ a, integral f = .elementary a ∧ a.Regular k ∧ a.deriv k t = val k f) ↔
      ∃ a : Answer R n, a.deriv k t = val k f := by
  constructor
  · rintro ⟨a, _, _, h⟩
    exact ⟨a, h⟩
  · rintro ⟨a, ha⟩
    have h := hs f
    cases hres : integral f with
    | elementary out =>
      rw [hres] at h
      exact ⟨out, rfl, h⟩
    | nonelementary =>
      rw [hres] at h
      exact (h (ha ▸ a.deriv_elementary k t)).elim

end SympyProofs.Calculus.Antiderivative
