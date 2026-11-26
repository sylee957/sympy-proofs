module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Model
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.OpenSet
import Mathlib.Tactic.FieldSimp

/-! The Möbius coordinate change at regular points of a native mixed tower over ℂ. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] {n : ℕ}

namespace Points

/-- Which original generators use the fractional linear tangent substitution. -/
def tangentAt : {m : ℕ} → Tower R m → Fin m → Bool
  | _, .base => Fin.elim0
  | _, .step t g => Fin.lastCases (match g with | .tan _ => true | _ => false) (tangentAt t)

/-- The original tangent as a rational function of the affine coordinate. -/
def original {F : Type} [Field F] (tan : Bool) (j x : F) : F :=
  if tan then -j*(x-1)/(x+1) else x

/-- The affine coordinate as a rational function of the tangent. -/
def affine {F : Type} [Field F] (tan : Bool) (j y : F) : F :=
  if tan then (j-y)/(j+y) else y

/-- Read a native complex point in the coordinates of the compiled affine tower. -/
noncomputable def point (t : Tower R n) (p : Fin n → ℂ) (i : Fin n) : ℂ :=
  affine (tangentAt t i) Complex.I (p i)

private theorem regular_tangent (t : Tower R n) (p : Fin n → ℂ) (hp : t.Nondegenerate p)
    (i : Fin n) (ht : tangentAt t i = true) : p i ≠ Complex.I ∧ p i ≠ -Complex.I := by
  induction t with
  | base => exact i.elim0
  | @step m t g ih =>
    apply Fin.lastCases (motive := fun j => tangentAt (t.step g) j = true →
      p j ≠ Complex.I ∧ p j ≠ -Complex.I) _ _ i ht
    · cases g <;> simp_all [tangentAt,Tower.Nondegenerate]
    · intro a ha
      exact ih (p ∘ Fin.castSucc) hp.lower a (by simpa [tangentAt] using ha)

private theorem affine_original {F : Type} [Field F] [CharZero F] {j x : F}
    (hj : j ≠ 0) (hx : x+1 ≠ 0) : affine true j (original true j x) = x := by
  have hd : j + -j*(x-1)/(x+1) = (2*j)/(x+1) := by field_simp; ring
  rw [affine,original,ite_eq_left rfl,ite_eq_left rfl,hd]
  field_simp
  ring

private theorem inverse_denom {j y : ℂ} (hj : j ≠ 0) (hy : j+y ≠ 0) :
    affine true j y + 1 ≠ 0 := by
  rw [affine,ite_eq_left rfl,div_add_one hy]
  apply div_ne_zero _ hy
  convert mul_ne_zero (two_ne_zero (α := ℂ)) hj using 1
  ring

private theorem original_affine {j y : ℂ} (hj : j ≠ 0) (hy : j+y ≠ 0) :
    original true j (affine true j y) = y := by
  have hd := inverse_denom hj hy
  simp only [original,affine,ite_true] at *
  field_simp
  ring_nf
  rw [mul_right_comm, mul_inv_cancel₀ hj,one_mul]

/-- The model rational function represented by a generator coordinate. -/
noncomputable abbrev X (i : Fin n) : M ℂ n := Model.polynomial ℂ (MvPolynomial.X i)

private theorem lift_X (i : Fin n) : Model.includeVars (Nat.le_succ n) (X i) = X i.castSucc := by
  simp [X,Model.polynomial]
  rfl

private theorem value_X (p : Fin n → ℂ) (i : Fin n) : Model.HasValue p (X i) (p i) := by
  simpa [X] using Model.HasValue.polynomial (p := p) (MvPolynomial.X i)

/-- The formal field isomorphism sends each generator to its own forward coordinate. -/
private theorem change_X (t : Tower R n) (i : Fin n) :
    t.changeModel ℂ Complex.I Complex.I_ne_zero (X i) =
      original (tangentAt t i) (Model.C ℂ n Complex.I) (X i) := by
  induction t with
  | base => exact i.elim0
  | @step m t g ih =>
    refine Fin.lastCases ?_ (fun a => ?_) i
    · apply (Model.stepEquiv ℂ m).injective
      cases g <;> simp [Tower.changeModel,changeStep,tangentAt,X,original,Model.polynomial,
        tangentValue,Model.stepEquiv_scalar]
    · rw [← lift_X,Tower.changeModel_lift,ih]
      simp only [tangentAt,Fin.lastCases_castSucc]
      cases tangentAt t a <;> simp [original]

private theorem inverse_X (t : Tower R n) (i : Fin n) :
    (t.changeModel ℂ Complex.I Complex.I_ne_zero).symm (X i) =
      affine (tangentAt t i) (Model.C ℂ n Complex.I) (X i) := by
  apply (t.changeModel ℂ Complex.I Complex.I_ne_zero).symm_apply_eq.mpr
  symm
  cases ht : tangentAt t i <;> simp only [affine,Bool.false_eq_true,ite_false,ite_true,
    map_div₀,map_sub,map_add,Tower.changeModel_C,change_X,ht]
  · rfl
  · have hn : X i+1 ≠ 0 := by
      intro hz
      have h := (value_X (fun _ => 0) i).add (Model.HasValue.C 1)
      simp only [map_one, zero_add, hz] at h
      exact one_ne_zero (h.unique Model.HasValue.zero)
    exact affine_original ((map_ne_zero_iff _ (Model.C ℂ n).injective).mpr Complex.I_ne_zero) hn

/-- Every inverse formal coordinate has its explicit value at native nondegenerate points. -/
theorem inverse_value (t : Tower R n) (p : Fin n → ℂ) (hp : t.Nondegenerate p) (i : Fin n) :
    Model.HasValue p ((t.changeModel ℂ Complex.I Complex.I_ne_zero).symm (X i))
      (point t p i) := by
  rw [inverse_X]
  simp only [point]
  cases ht : tangentAt t i with
  | false => exact value_X p i
  | true =>
    have h := (regular_tangent t p hp i ht).2
    exact ((Model.HasValue.C Complex.I).sub (value_X p i)).div
      ((Model.HasValue.C _).add (value_X p i)) (fun e => h (eq_neg_of_add_eq_zero_right e))

private theorem forward_value (t : Tower R n) (p : Fin n → ℂ) (hp : t.Nondegenerate p)
    (i : Fin n) :
    Model.HasValue (point t p) (t.changeModel ℂ Complex.I Complex.I_ne_zero (X i)) (p i) := by
  rw [change_X]
  have hv := value_X (point t p) i
  simp only [point] at hv
  cases ht : tangentAt t i with
  | false => simpa [ht,affine,original] using hv
  | true =>
    have h : Complex.I+p i ≠ 0 := fun e =>
      (regular_tangent t p hp i ht).2 (eq_neg_of_add_eq_zero_right e)
    rw [ht] at hv
    have v := (((Model.HasValue.C Complex.I).neg).mul (hv.sub (Model.HasValue.C 1))).div
      (hv.add (Model.HasValue.C 1)) (inverse_denom Complex.I_ne_zero h)
    simp only [map_one] at v
    change Model.HasValue (point t p) (original true _ (X i))
      (original true Complex.I (affine true Complex.I (p i))) at v
    rwa [original_affine Complex.I_ne_zero h] at v

/-- A fraction regular in the native chart has the same value after the coordinate change. -/
theorem change_value (t : Tower R n) (p : Fin n → ℂ) (hp : t.Nondegenerate p) {x : M ℂ n}
    {c : ℂ} (hx : Model.HasValue p x c) :
    Model.HasValue (point t p) (t.changeModel ℂ Complex.I Complex.I_ne_zero x) c := by
  let e := t.changeModel ℂ Complex.I Complex.I_ne_zero
  have poly (a : MvPolynomial (Fin n) ℂ) :
      Model.HasValue (point t p) (e (Model.polynomial ℂ a)) (MvPolynomial.eval p a) := by
    induction a using MvPolynomial.induction_on with
    | C a =>
      change Model.HasValue _ (e (Model.C ℂ n a)) (MvPolynomial.eval p (MvPolynomial.C a))
      rw [MvPolynomial.eval_C, show e (Model.C ℂ n a) = _ from t.changeModel_C ℂ _ _ a]
      exact Model.HasValue.C _
    | add a b ha hb => simpa only [Model.polynomial,map_add] using ha.add hb
    | mul_X a i ha =>
      simpa only [X,Model.polynomial,map_mul,MvPolynomial.eval_X] using
        ha.mul (forward_value t p hp i)
  obtain ⟨a,b,hx,hb,ha⟩ := hx
  have hbn : Model.polynomial ℂ b ≠ 0 := by
    rintro h
    have hz : b = 0 := (IsFractionRing.injective _ (M ℂ n)) (h.trans (map_zero _).symm)
    simp [hz] at hb
  have h := (poly a).div (poly b) hb
  rwa [← map_div₀,(div_eq_iff hbn).mpr hx,ha,mul_div_cancel_right₀ _ hb] at h

private theorem point_lower (t : Tower R n) (g : Gen (K R n)) (p : Fin (n+1) → ℂ) :
    point (t.step g) p ∘ Fin.castSucc = point t (p ∘ Fin.castSucc) := by
  funext i
  simp [point,tangentAt]

/-- A nondegenerate native point has nonvanishing exponential coordinates in the compiler. -/
theorem nondegenerate {S : Type} [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S]
    [Div S] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
    (c : K R 0 → K S 0) (i : K S 0) (t : Tower R n) (p : Fin n → ℂ) (hp : t.Nondegenerate p) :
    (t.compile c i).tower.Nondegenerate (point t p) := by
  induction t with
  | base => trivial
  | @step m t g ih =>
    have low := ih _ hp.lower
    cases g with
    | prim _ => simpa only [Tower.compile,Tower.Nondegenerate,point_lower] using low
    | exp _ =>
      simp only [Tower.compile,Tower.Nondegenerate,point_lower]
      exact ⟨low,by simpa [point,tangentAt,affine] using hp.2⟩
    | tan _ =>
      simp only [Tower.compile,Kind.Tan.tower,Tower.Nondegenerate,point_lower]
      apply And.intro low
      simp only [point,tangentAt,Fin.lastCases_last,affine,ite_true]
      exact div_ne_zero (sub_ne_zero.mpr hp.2.1.symm) (fun h => hp.2.2
        (eq_neg_of_add_eq_zero_right h))

end Points

end SympyProofs.Calculus.Antiderivative.Trigonometric
