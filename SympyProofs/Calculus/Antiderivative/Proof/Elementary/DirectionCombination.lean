module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Combinations

/-! The reduction identity for arbitrary combinations of residue directions, including
coefficients in a larger model. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Solve Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Interpretation of a Laurent numerator is linear over the model's constant field. -/
noncomputable def laurentMap (s : ℕ) : Polynomial (M k n) →ₗ[k] M k (n+1) where
  toFun := laurentValue k s
  map_add' := laurentValue_add k s
  map_smul' c p := by
    have hp : c • p = C (Model.C k n c) * p := by rw [Algebra.smul_def]; rfl
    rw [hp, RingHom.id_apply, Model.smul_eq_C_mul]
    apply (Model.stepEquiv k n).injective
    rw [map_mul, Model.stepEquiv_scalar]
    simp [laurentValue, mul_div_assoc]

/-- The input combination splits into the derivatives of the recorded answers and the
Laurent remainder at every choice of direction coordinates. -/
theorem DirectionSpec.combination_identity {t : Tower R n} {g : ReducedGen (K R n)}
    {s : ℕ} {gs : List (K R (n+1))} {ds : List (Direction R n)}
    (hd : DirectionSpec k t g gs s ds) (v : Fin ds.length → k) :
    Linear.accumulate gs (val k) (Linear.accumulate ds
        (fun d => Linear.vector (Model.constantHom k) gs.length d.coords) v) =
      Linear.accumulate ds (fun d => d.answer.deriv k (t.step g)) v +
        laurentValue k s (Linear.accumulate ds (fun d => modelPoly k d.rest) v) := by
  change _ = _ + laurentMap k s _
  rw [Linear.map_accumulate, Linear.map_accumulate]
  simp only [Linear.accumulate_apply, ← Finset.sum_add_distrib, ← smul_add]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (v i • ·)
  rw [← Linear.accumulate_apply gs (val k)
    (Linear.vector (Model.constantHom k) _ (ds.get i).coords)]
  rw [Model.accumulate_constants k _ _ (hd.width _ (ds.get_mem i))]
  exact (hd.identity _ (ds.get_mem i)).symm

/-- The Liouville forms of a tower form a vector subspace over its constants. -/
noncomputable def elementarySpace (t : Tower R n) : Submodule k (M k n) where
  carrier := {x | t.Elementary k x}
  zero_mem' := Tower.Elementary.zero k t
  add_mem' := Tower.Elementary.add k
  smul_mem' c _ hx := (Model.smul_eq_C_mul k c _).symm ▸ Tower.Elementary.mul_const k c hx

/-- The original combination has an elementary integral exactly when the Laurent remainder does. -/
theorem DirectionSpec.elementary_iff {t : Tower R n} {g : ReducedGen (K R n)}
    {s : ℕ} {gs : List (K R (n+1))} {ds : List (Direction R n)}
    (hd : DirectionSpec k t g gs s ds) (v : Fin ds.length → k) :
    (t.step g).Elementary k (Linear.accumulate gs (val k) (Linear.accumulate ds
        (fun d => Linear.vector (Model.constantHom k) gs.length d.coords) v)) ↔
      (t.step g).Elementary k
        (laurentValue k s (Linear.accumulate ds (fun d => modelPoly k d.rest) v)) := by
  rw [hd.combination_identity]
  let A := Linear.accumulate ds (fun d => d.answer.deriv k (t.step g)) v
  have ha : (t.step g).Elementary k A := by
    change A ∈ elementarySpace k (t.step g)
    rw [show A = _ from Linear.accumulate_apply ..]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      ((ds.get i).answer.deriv_elementary k (t.step g))
  constructor
  · intro h
    simpa only [A, add_sub_cancel_left] using (h.sub k ha)
  · exact fun h => ha.add k h

end SympyProofs.Calculus.Antiderivative.Elementary
