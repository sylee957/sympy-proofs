module

public import SympyProofs.Calculus.Antiderivative.Proof.StepModel
public import SympyProofs.Calculus.Antiderivative.Proof.BaseLevel
public import SympyProofs.Calculus.Antiderivative.Spec.Admissible
import SympyProofs.Calculus.Antiderivative.Extension.Constants

/-! The constants of an admissible tower are exactly its model coefficient field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

@[simp] theorem modelD_C (t : Tower R n) (c : k) :
    t.modelD k (Model.C k n c) = 0 :=
  Model.derivation_C k _ _

/-- At height zero every model fraction is already a coefficient. -/
@[simp] theorem admissible_base : (base : Tower R 0).Admissible k := by
  intro x
  obtain ⟨c, rfl⟩ := Model.C_surjective_zero k x
  exact ⟨fun _ => ⟨c, rfl⟩, fun _ => modelD_C k _ c⟩

variable [CharZero k]

/-- A rational function with zero derivative at an admissible step belongs to the lower field. -/
theorem exists_includeVars_of_modelD_eq_zero (t : Tower R n) (g : ReducedGen (K R n))
    (hg : g.Admissible k t) {x : M k (n + 1)} (hx : (t.step g).modelD k x = 0) :
    ∃ a : M k n, x = Model.includeVars (Nat.le_succ n) a ∧ t.modelD k a = 0 := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have hd := (stepEquiv_modelD k t g x).symm
  rw [hx, map_zero] at hd
  have hc : ∃ a : M k n, Model.stepEquiv k n x = RatFunc.C a := by
    cases g with
    | prim b =>
      apply Extension.constant_of_prim (b := val k b) hg
      simpa [Extension.affine, Model.extendVariable, modelVelocity] using hd
    | exp u =>
      apply Extension.constant_of_exp (a := val k (t.D u)) hg
      simpa [Extension.affine, Model.extendVariable, modelVelocity] using hd
  obtain ⟨a, ha⟩ := hc
  rw [ha, Model.extendVariable_C] at hd
  refine ⟨a, (Model.stepEquiv k n).injective ?_, RatFunc.C_injective (hd.trans (map_zero _).symm)⟩
  rw [Model.stepEquiv_includeVars, ha]

/-- An admissible primitive or exponential extension preserves the constants of its base. -/
theorem admissible_step (t : Tower R n) (g : ReducedGen (K R n))
    (ht : t.Admissible k) (hg : g.Admissible k t) : (t.step g).Admissible k := by
  intro x
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨a, rfl, ha⟩ := t.exists_includeVars_of_modelD_eq_zero k g hg hx
    obtain ⟨c, rfl⟩ := (ht a).mp ha
    exact ⟨c, Model.includeVars_C k _ c⟩
  · rintro ⟨c, rfl⟩
    exact modelD_C k _ c

end SympyProofs.Calculus.Antiderivative.Tower
