module

public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants
public import SympyProofs.Calculus.Antiderivative.Extension.LiouvilleForm
import Mathlib.Algebra.BigOperators.Fin

/-! Transport the finite logarithmic-derivative criterion to the one-variable presentation,
where the general primitive and exponential polynomial criteria apply. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

omit [CharZero k] in
private theorem elementary_transport (t : Tower R n) {F L : Type} [Field F] [Field L]
    [Differential F] [Differential L] [Algebra F L] (e : M k n ≃+* L)
    (hD : ∀ x, e (t.modelD k x) = Differential.deriv (e x))
    (hC : ∀ c : k, ∃ a : F, Differential.deriv a = 0 ∧ algebraMap F L a = e (Model.C k n c))
    (hF : ∀ a : F, Differential.deriv a = 0 → ∃ c : k, algebraMap F L a = e (Model.C k n c))
    (x : M k n) : t.Elementary k x ↔ Extension.LiouvilleForm.InLiouvilleForm F (e x) := by
  classical
  constructor
  · rintro ⟨y,logs,h⟩
    choose coeff hcoeff hcoeff' using hC
    let term (s : k × M k n) := Model.C k n s.1 * (t.modelD k s.2 / s.2)
    have hs : (logs.map term).sum = ∑ i : Fin logs.length, term (logs.get i) := by
      rw [← Fin.sum_ofFn]
      change _ = (List.ofFn (term ∘ logs.get)).sum
      rw [← List.map_ofFn, List.ofFn_get]
    refine ⟨Fin logs.length, inferInstance, fun i => coeff (logs.get i).1,
      fun i => hcoeff _, fun i => e (logs.get i).2, e y, ?_⟩
    change x = t.modelD k y + (logs.map term).sum at h
    rw [h, hs, map_add, map_sum, hD, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [term, hcoeff', Differential.logDeriv, hD]
  · rintro ⟨ι, hι, c, hc, u, y, h⟩
    choose d hd using fun i => hF (c i) (hc i)
    refine ⟨e.symm y, Finset.univ.toList.map (fun i => (d i, e.symm (u i))), e.injective ?_⟩
    rw [List.map_map, Finset.sum_map_toList, map_add, map_sum, hD, e.apply_symm_apply, add_comm, h]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [hd, Differential.logDeriv, hD]

omit [CharZero k] in
/-- The ground constants of an admissible tower give the usual differential-field
Liouville form for its elements. -/
theorem elementary_iff_form (t : Tower R n) (ht : t.Admissible k) (x : M k n) :
    t.Elementary k x ↔
      (letI : Differential (M k n) := ⟨t.modelD k⟩
       Extension.LiouvilleForm.InLiouvilleForm (M k n) x) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  apply elementary_transport k t (RingEquiv.refl _) (fun _ => rfl)
  · intro c
    exact ⟨Model.C k n c, modelD_C k t c, rfl⟩
  · intro a ha
    exact (ht a).mp ha

omit [CharZero k] in
/-- In the top-variable presentation only constants of the lower field are needed as weights. -/
theorem elementary_iff_stepForm (t : Tower R n) (g : Gen (K R n))
    (ht : t.Admissible k) (x : M k (n+1)) :
    (t.step g).Elementary k x ↔
      (letI : Differential (M k n) := ⟨t.modelD k⟩
       letI : Differential (RatFunc (M k n)) :=
         ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k g)⟩
       Extension.LiouvilleForm.InLiouvilleForm (M k n) (Model.stepEquiv k n x)) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k g)⟩
  have h (c : k) : algebraMap (M k n) (RatFunc (M k n)) (Model.C k n c) =
      Model.stepEquiv k n (Model.C k (n+1) c) := by
    rw [RatFunc.algebraMap_eq_C, ← Model.stepEquiv_includeVars, Model.includeVars_C]
  apply elementary_transport k _ (Model.stepEquiv k n) (stepEquiv_modelD k t g)
  · intro c
    exact ⟨Model.C k n c, modelD_C k t c, h c⟩
  · intro a ha
    obtain ⟨c,rfl⟩ := (ht a).mp ha
    exact ⟨c,h c⟩

/-- A primitive polynomial in Liouville form is characterized by a finite triangular system
and a lower-field constant term with a Liouville form. -/
theorem elementary_prim_polynomial_iff (t : Tower R n) (b : K R n)
    (ht : t.Admissible k) (hb : (ReducedGen.prim b).Admissible k t) (q : Polynomial (M k n)) :
    (t.step (.prim b)).Elementary k ((Model.stepEquiv k n).symm (algebraMap _ _ q)) ↔
      ∃ p : Polynomial (M k n), p.natDegree ≤ q.natDegree+1 ∧
        t.Elementary k (q.coeff 0 - val k b * p.coeff 1) ∧
        ∀ i : ℕ, i ≤ q.natDegree →
          t.modelD k (p.coeff (i+1)) + ((i+2 : ℕ) : M k n) * val k b * p.coeff (i+2) =
            q.coeff (i+1) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k (.prim b))⟩
  let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) :=
    ⟨fun a => Model.extendVariable_C _ _ a⟩
  have dx : Differential.deriv (RatFunc.X : RatFunc (M k n)) = RatFunc.C (val k b) := by
    change Model.extendVariable _ _ _ = _
    simp [modelVelocity]
  rw [elementary_iff_stepForm k t _ ht, RingEquiv.apply_symm_apply]
  refine (Extension.LiouvilleForm.primitive_polynomial_iff _ hb dx q).trans ?_
  refine exists_congr fun p => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  exact (elementary_iff_form k t ht _).symm

omit [CharZero k] in
/-- All nonconstant Laurent coefficients of an elementary integrand in an exponential step
satisfy lower Risch differential equations. Its constant coefficient is elementary below. -/
theorem elementary_exp_laurent_necessary (t : Tower R n) (u : K R n)
    (ht : t.Admissible k) (q : Polynomial (M k n)) (s : ℕ)
    (h : (t.step (.exp u)).Elementary k
      ((Model.stepEquiv k n).symm (algebraMap _ _ q / RatFunc.X ^ s))) :
    t.Elementary k (q.coeff s) ∧ ∀ j : ℕ, j ≠ s → ∃ y : M k n,
      t.modelD k y + ((j : M k n) - s) * val k (t.D u) * y = q.coeff j := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k (.exp u))⟩
  let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) :=
    ⟨fun a => Model.extendVariable_C _ _ a⟩
  have dx : Differential.deriv (RatFunc.X : RatFunc (M k n)) =
      RatFunc.C (Differential.deriv (val k u)) * RatFunc.X := by
    change Model.extendVariable _ _ _ = RatFunc.C (t.modelD k (val k u)) * RatFunc.X
    simp [modelVelocity]
  rw [elementary_iff_stepForm k t _ ht, RingEquiv.apply_symm_apply] at h
  obtain ⟨h₀,hpos⟩ := Extension.LiouvilleForm.exponential_laurent_necessary (val k u) dx q s h
  refine ⟨(elementary_iff_form k t ht _).mpr h₀, ?_⟩
  rw [val_D]
  exact hpos

end SympyProofs.Calculus.Antiderivative.Tower

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- A negative verdict of a complete integrator rules out a primitive in every elementary
differential field extension of an admissible model. -/
theorem Tower.IntegrateSpec.no_primitive {t : Tower R n} {integral : K R n → Result R n}
    (hs : t.IntegrateSpec k integral) (ht : t.Admissible k) {f : K R n}
    (h : integral f = .nonelementary) :
    letI : Differential (M k n) := ⟨t.modelD k⟩
    ∀ (E : Type) [Field E] [Differential E] [Algebra (M k n) E],
      Extension.LiouvilleForm.ElementaryTower (M k n) E →
        ∀ y : E, Differential.deriv y ≠ algebraMap (M k n) E (val k f) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  intro E _ _ _ tower y hy
  have hc := hs f
  rw [h] at hc
  exact hc ((t.elementary_iff_form k ht _).mpr (tower.form_of_primitive _ y hy))

end SympyProofs.Calculus.Antiderivative
