module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Model
public import SympyProofs.Calculus.Antiderivative.Proof.DecisionLevel

/-! Elementary integration and parametric differential equations in the native tangent
coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Trigonometric

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]
variable [Algebra S k] [FaithfulSMul S k] [CharZero S]

omit [CharZero k] in
private theorem map_liouville (e : M k n ≃+* M k n) (D E : Model.Der (M k n))
    (hD : ∀ x, e (D x) = E (e x)) (hC : ∀ c, e (Model.C k n c) = Model.C k n c)
    {f x : M k n} (logs : List (k × M k n))
    (h : f = D x + (logs.map fun (c, u) => Model.C k n c * (D u / u)).sum) :
    e f = E (e x) + ((logs.map fun (c, u) => (c,e u)).map fun (c, u) =>
      Model.C k n c * (E u / u)).sum := by
  have hl : e ((logs.map fun (c, u) => Model.C k n c * (D u / u)).sum) =
      ((logs.map fun (c, u) => (c,e u)).map fun (c, u) => Model.C k n c * (E u / u)).sum := by
    clear h
    induction logs with
    | nil => simp
    | cons a l ih => rcases a with ⟨c,u⟩; simp only [List.map_cons, List.sum_cons, map_add,
        map_mul, map_div₀, hC, hD]; rw [ih]
  rw [h, map_add, hD, hl]

variable (c : K R 0 →+* K S 0) (hc : ∀ a, Model.constantHom k (c a) = Model.constantHom k a)
variable (i : K S 0) (hi : i ^ 2 = -1)
include hc hi

/-- Coordinate change preserves existence of a Liouville form in both directions, allowing
arbitrary model coefficients and logarithmic arguments. -/
theorem Tower.elementary_iff (t : Tower R n) (f : M k n) :
    t.Elementary k f ↔ (t.compile c i).tower.Elementary k
      (t.changeModel k (Model.constantHom k i) (constant_ne k i hi) f) := by
  let e := t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
  let D := t.modelD k
  let E := (t.compile c i).tower.modelD k
  have hd (x) : e (D x) = E (e x) := t.changeModel_D k c hc i hi x
  have hs (a) : e (Model.C k n a) = Model.C k n a := t.changeModel_C k _ _ a
  constructor
  · rintro ⟨x,l,h⟩
    exact ⟨e x,_,map_liouville k e D E hd hs l h⟩
  · rintro ⟨x,l,h⟩
    have hd' (y) : e.symm (E y) = D (e.symm y) := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply, hd, RingEquiv.apply_symm_apply]
    have hs' (a) : e.symm (Model.C k n a) = Model.C k n a := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply, hs]
    refine ⟨e.symm x,l.map (fun (a,u) => (a,e.symm u)),?_⟩
    simpa only [e, RingEquiv.symm_apply_apply] using map_liouville k e.symm E D hd' hs' l h

/-- Elementary existence on a native input is exactly elementary existence on the compiled
input. -/
theorem Tower.elementary_value_iff (t : Tower R n) (x : K R n) :
    t.Elementary k (val k x) ↔ (t.compile c i).tower.Elementary k
      (val k ((t.compile c i).value x)) := by
  rw [t.elementary_iff k c hc i hi, t.changeModel_val k c hc i hi, t.compileHom_apply]

theorem Tower.changeModel_linearCombination (t : Tower R n) (cs : List k) (gs : List (K R n)) :
    t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
      (Model.linearCombination k cs gs) =
        Model.linearCombination k cs (gs.map (t.compile c i).value) := by
  induction cs generalizing gs with
  | nil => simp [Model.linearCombination]
  | cons a cs ih => cases gs with
    | nil => simp [Model.linearCombination]
    | cons g gs =>
      simp only [Model.linearCombination, List.map_cons, map_add, map_mul,
        t.changeModel_C k (Model.constantHom k i) (constant_ne k i hi),
        t.changeModel_val k c hc i hi, t.compileHom_apply, ih]

/-- The coordinate equivalence bijects all solutions of each parametric linear equation; the
parameter vector is unchanged. -/
theorem Tower.rde_iff (t : Tower R n) (x : M k n) (f : K R n) (gs : List (K R n)) (cs : List k) :
    let e := t.changeModel k (Model.constantHom k i) (constant_ne k i hi)
    let u := t.compile c i
    t.modelD k x + val k f * x = Model.linearCombination k cs gs ↔
      u.tower.modelD k (e x) + val k (u.value f) * e x =
        Model.linearCombination k cs (gs.map u.value) := by
  dsimp only
  rw [← (t.changeModel k (Model.constantHom k i) (constant_ne k i hi)).injective.eq_iff]
  rw [map_add, map_mul, t.changeModel_D k c hc i hi, t.changeModel_val k c hc i hi,
    t.compileHom_apply, t.changeModel_linearCombination k c hc i hi]

variable [IsAlgClosed k] [NatBound (K S 0)] [LawfulNatBound (K S 0)]
variable [IntegerRelations (K S 0)] [LawfulIntegerRelations (K S 0)]
variable [ConstantFactors (K S 0)] [LawfulConstantFactors (K S 0)]

omit hc hi [Algebra R k] [FaithfulSMul R k] [CharZero S] [DecidableEq R]
  [NormalizedGCDMonoid R] [Div R] in
private theorem Trigonometric.Compiled.integral_spec (u : Compiled R S n) (x : K R n)
    (r : Result S n)
    (h : u.integrate x = some r) :
    match r with
    | .elementary a => a.Regular k ∧ a.deriv k u.tower = val k (u.value x)
    | .nonelementary => ¬ u.tower.Elementary k (val k (u.value x)) := by
  unfold Compiled.integrate at h
  split at h
  · rename_i hb
    have ht := (u.tower.checkSteps_iff k u.tangentFree).mp hb
    have hs := (u.tower.level_spec k u.tangentFree ht).integrate (u.value x)
    rw [Option.some.inj h] at hs
    cases r <;> exact hs
  · contradiction

/-- A checked positive result is regular and its derivative is the image of the original
input under the mixed coordinate change. -/
theorem Tower.compile_integrate_sound (t : Tower R n) (x : K R n) (a : Answer S n)
    (h : (t.compile c i).integrate x = some (.elementary a)) :
    a.Regular k ∧ a.deriv k (t.compile c i).tower =
      t.changeModel k (Model.constantHom k i) (constant_ne k i hi) (val k x) := by
  rw [t.changeModel_val k c hc i hi, t.compileHom_apply]
  exact Compiled.integral_spec k _ x (.elementary a) h

/-- A checked negative result excludes every Liouville form in the original coordinates. -/
theorem Tower.compile_integrate_complete (t : Tower R n) (x : K R n)
    (h : (t.compile c i).integrate x = some .nonelementary) : ¬ t.Elementary k (val k x) := by
  rw [t.elementary_value_iff k c hc i hi]
  exact Compiled.integral_spec k _ x .nonelementary h

/-- The checked solver captures every solution in the original coordinates by its compiled
generators and constant rows. -/
theorem Tower.compile_solve_spec (t : Tower R n) (f : K R n) (gs : List (K R n))
    {out : List (K S n) × List (List (K S 0))} (h : (t.compile c i).solve f gs = some out)
    (y : M k n) (cs : List k) (hs : cs.length = gs.length) :
    t.modelD k y + val k f * y = Model.linearCombination k cs gs ↔
      ∃ d : List k, d.length = out.1.length ∧
        t.changeModel k (Model.constantHom k i) (constant_ne k i hi) y =
          Model.linearCombination k d out.1 ∧
        ∀ row ∈ out.2, Model.rowHolds k row (cs ++ d) := by
  unfold Compiled.solve at h
  split at h
  · rename_i hb
    cases h
    apply (t.rde_iff k c hc i hi y f gs cs).trans
    let u := t.compile c i
    have ht := (u.tower.checkSteps_iff k u.tangentFree).mp hb
    exact (u.tower.level_spec k u.tangentFree ht).solve _ _ _ _ (by simpa using hs)
  · contradiction

end SympyProofs.Calculus.Antiderivative
