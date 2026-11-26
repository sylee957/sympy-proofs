module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Inverse
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Transfer

/-! Semantics of field terms and logarithmic arguments in the original tangent coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k]

private theorem changeModel_shape (t : Tower R n) (j : k) (hj : j ≠ 0) :
    (t.shape S).changeModel k j hj = t.changeModel k j hj := by
  induction t with
  | base => rfl
  | step t g ih => cases g <;> simp only [Tower.shape, Tower.changeModel, ih]

variable [CharZero S] [Algebra S k] [FaithfulSMul S k]

/-- Model evaluation of the restored rational function reverses the compiler's isomorphism. -/
theorem Tower.changeModel_restore (t : Tower R n) (i : K S 0) (hi : i^2 = -1)
    (hj : Model.constantHom k i ≠ 0) (x : K S n) :
    t.changeModel k (Model.constantHom k i) hj (val k (t.restore i x)) = val k x := by
  rw [← changeModel_shape (S := S) k t]
  have h := (t.shape S).changeModel_val k (RingHom.id _) (fun _ => rfl) i hi (t.restore i x)
  change _ = val k (t.forward i hi (t.restore i x)) at h
  simpa only [t.forward_restore] using h

/-- Evaluation at any constant root respects the inverse substitution of every coefficient. -/
theorem Tower.changeModel_restoreArg (t : Tower R n) (i : K S 0) (hi : i^2 = -1)
    (hj : Model.constantHom k i ≠ 0) (s : RootSum S n) (c : k) :
    t.changeModel k (Model.constantHom k i) hj ((t.restoreSum i s).argAt k c) = s.argAt k c := by
  let e := t.changeModel k (Model.constantHom k i) hj
  have comp : e.toRingHom.comp ((val k).comp (t.restoreHom i hi)) = val k := by
    ext x
    change e (val k (t.restoreHom i hi x)) = _
    rw [t.restoreHom_apply]
    exact t.changeModel_restore k i hi hj x
  change e.toRingHom ((Poly.equiv (s.arg.map (t.restore i))).eval₂ (val k) (Model.C k n c)) = _
  rw [← funext (t.restoreHom_apply i hi), Poly.equiv_map, Polynomial.eval₂_map,
    Polynomial.hom_eval₂, comp]
  change _ = (Poly.equiv s.arg).eval₂ (val k) (Model.C k n c)
  rw [show e.toRingHom (Model.C k n c) = _ from t.changeModel_C k _ _ c]

/-- Rewriting a root sum preserves regularity at every root of the unchanged modulus. -/
theorem Tower.restore_regular (t : Tower R n) (i : K S 0) (hi : i^2 = -1)
    (hj : Model.constantHom k i ≠ 0) (a : Answer S n) :
    (t.restoreAnswer i a).Regular k ↔ a.Regular k := by
  simp only [Answer.Regular, restoreAnswer, List.forall_mem_map]
  apply forall_congr' fun s => forall_congr' fun _ => ?_
  refine and_congr_right fun _ => forall_congr' fun c => forall_congr' fun _ => ?_
  rw [← t.changeModel_restoreArg k i hi hj s c]
  exact (map_ne_zero_iff _ (RingEquiv.injective _)).symm

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R] [Algebra R k] [FaithfulSMul R k]

variable (c : K R 0 →+* K S 0) (hc : ∀ z, Model.constantHom k (c z) = Model.constantHom k z)
variable (i : K S 0) (hi : i^2 = -1) (hj : Model.constantHom k i ≠ 0)

include hc hi in
/-- Differentiating after restoration gives the original-coordinate value of the compiled
primitive's derivative, including every logarithmic root sum. -/
theorem Tower.changeModel_answerDerivative (t : Tower R n) (a : Answer S n) :
    t.changeModel k (Model.constantHom k i) hj (Answer.deriv k t (t.restoreAnswer i a)) =
      a.deriv k (t.compile c i).tower := by
  classical
  let e := t.changeModel k (Model.constantHom k i) hj
  have D (x : M k n) : e (t.modelD k x) = (t.compile c i).tower.modelD k (e x) :=
    t.changeModel_D k c hc i hi x
  have scal (b : k) : e (Model.C k n b) = Model.C k n b := t.changeModel_C k _ _ b
  have weight (w : K S 0) : e (val k (K.ofConst w)) = val k (K.ofConst w) := by
    rw [← Model.C_constantHom, scal]
  have root (s : RootSum S n) :
      e (RootSum.deriv k t (t.restoreSum i s)) = s.deriv k (t.compile c i).tower := by
    simp only [RootSum.deriv, restoreSum, RootSum.modelModulus, map_mul,
      map_sum, D, map_div₀, scal, weight]
    apply congrArg (_ * ·)
    apply Finset.sum_congr rfl
    intro z _
    change _ * ((t.compile c i).tower.modelD k (e ((t.restoreSum i s).argAt k z)) /
      e ((t.restoreSum i s).argAt k z)) = _
    rw [show e ((t.restoreSum i s).argAt k z) = _ from t.changeModel_restoreArg k i hi hj s z]
  change e (t.modelD k (val k (t.restore i a.field)) + _) = _
  simp only [map_add, D, show e (val k (t.restore i a.field)) = _ from
    t.changeModel_restore k i hi hj a.field, Answer.deriv, map_list_sum, List.map_map,
    Function.comp_def, root, Tower.restoreAnswer]


omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] [Algebra R k] [FaithfulSMul R k] in
include hi in
private theorem restore_combination (t : Tower R n) (ds : List k) (xs : List (K S n)) :
    t.changeModel k (Model.constantHom k i) hj
      (Model.linearCombination k ds (xs.map (t.restore i))) = Model.linearCombination k ds xs := by
  induction ds generalizing xs with
  | nil => simp [Model.linearCombination]
  | cons d ds ih => cases xs with
    | nil => simp [Model.linearCombination]
    | cons x xs =>
      simp only [List.map_cons, Model.linearCombination, map_add, map_mul, Tower.changeModel_C,
        t.changeModel_restore k i hi hj, ih]

variable [IsAlgClosed k] [NatBound (K S 0)] [LawfulNatBound (K S 0)]
variable [IntegerRelations (K S 0)] [LawfulIntegerRelations (K S 0)]
variable [ConstantFactors (K S 0)] [LawfulConstantFactors (K S 0)]

include hc hi

/-- Every returned primitive is regular and differentiates to the input in the native
mixed tower, using the tangent chain rule at each tangent generator. -/
theorem Tower.integrateOriginal_sound (t : Tower R n) (f : K R n) (a : Answer S n)
    (h : t.integrateOriginal c i f = some (.elementary a)) :
    a.Regular k ∧ Answer.deriv k t a = val k f := by
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h
  cases v with
  | nonelementary => contradiction
  | elementary v =>
    cases he
    obtain ⟨reg, der⟩ := t.compile_integrate_sound k c hc i hi f v hv
    refine ⟨(t.restore_regular k i hi (constant_ne k i hi) v).mpr reg, ?_⟩
    apply (t.changeModel k _ (constant_ne k i hi)).injective
    exact (t.changeModel_answerDerivative k c hc i hi _ v).trans der

/-- A negative integration decision excludes every Liouville form in native coordinates. -/
theorem Tower.integrateOriginal_complete (t : Tower R n) (f : K R n)
    (h : t.integrateOriginal c i f = some .nonelementary) :
    ¬ t.Elementary k (val k f) := by
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h
  cases v with
  | elementary => contradiction
  | nonelementary => exact t.compile_integrate_complete k c hc i hi f hv

/-- The restored solution generators and the returned constant constraints describe exactly
the solutions of the input parametric differential equation in its original coordinates. -/
theorem Tower.solveOriginal_spec (t : Tower R n) (f : K R n) (gs : List (K R n))
    {out : List (K S n) × List (List (K S 0))} (h : t.solveOriginal c i f gs = some out)
    (y : M k n) (cs : List k) (hs : cs.length = gs.length) :
    t.modelD k y + val k f * y = Model.linearCombination k cs gs ↔
      ∃ ds : List k, ds.length = out.1.length ∧ y = Model.linearCombination k ds out.1 ∧
        ∀ row ∈ out.2, Model.rowHolds k row (cs ++ ds) := by
  obtain ⟨⟨xs, rows⟩, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [t.compile_solve_spec k c hc i hi f gs hv y cs hs]
  simp only [List.length_map]
  refine exists_congr fun ds => and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [← restore_combination k i hi (constant_ne k i hi) t ds xs,
    (t.changeModel k _ _).injective.eq_iff]

end SympyProofs.Calculus.Antiderivative
