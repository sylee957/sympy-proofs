module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Answer
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Model
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Scale
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Trace

/-! Two simultaneous interpretations of the same quadratic logarithmic sum. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

open Polynomial

/-- The two maps which evaluate a logarithmic modulus and its argument. Bundling the maps
permits both embeddings of the quadratic coefficient field in the same statement. -/
structure Interpretation (S k : Type) (n : ℕ) [CommRing S] [IsDomain S] [DecidableEq S]
    [NormalizedGCDMonoid S] [Div S] [Field k] where
  /-- Evaluation of constant coefficients. -/
  scalar : K S 0 →+* k
  /-- Evaluation of rational tower functions. -/
  field : K S n →+* M k n

variable {S : Type} [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S]
variable {k : Type} [Field k] {n : ℕ}

namespace Interpretation

/-- Interpret the polynomial whose distinct roots index this sum. -/
noncomputable def modulus (J : Interpretation S k n) (s : RootSum S n) : k[X] :=
  Step.modelPoly J.scalar s.modulus

/-- Evaluate the logarithmic argument at the chosen model root. -/
noncomputable def argument (J : Interpretation S k n) (s : RootSum S n) (z : k) : M k n :=
  Step.atRoot J.field (Model.C k n z) s.arg

/-- Every logarithmic argument at a root is nonzero. -/
def Regular (J : Interpretation S k n) (s : RootSum S n) : Prop :=
  J.modulus s ≠ 0 ∧ ∀ z, (J.modulus s).IsRoot z → J.argument s z ≠ 0

/-- Evaluate the finite sum of logarithmic derivatives. -/
noncomputable def derivative (J : Interpretation S k n) (D : Model.Der (M k n))
    (s : RootSum S n) : M k n := by
  classical
  exact Model.C k n (J.scalar s.weight) * ∑ z ∈ (J.modulus s).roots.toFinset,
    Model.C k n z * (D (J.argument s z) / J.argument s z)

variable (k) [Algebra S k] [FaithfulSMul S k]

/-- The standard interpretation supplied by a coefficient algebra in the model. -/
noncomputable def standard : Interpretation S k n := ⟨Model.constantHom k,val k⟩

@[simp] theorem standard_modulus (s : RootSum S n) :
    (standard k).modulus s = s.modelModulus k := rfl

@[simp] theorem standard_argument (s : RootSum S n) (z : k) :
    (standard k).argument s z = s.argAt k z := by
  simp [argument,standard,Step.atRoot,RootSum.argAt,eval_map]

@[simp] theorem standard_regular (s : RootSum S n) :
    (standard k).Regular s ↔ s.Regular k := by simp [Regular,RootSum.Regular]

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R k] [FaithfulSMul R k]

@[simp] theorem standard_derivative (t : Tower R n) (s : RootSum S n) :
    (standard k).derivative (t.modelD k) s = RootSum.deriv k t s := by
  simp only [derivative,standard_argument,standard_modulus,RootSum.deriv]
  rw [← Model.C_constantHom]
  rfl

end Interpretation

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] [Algebra R k] [FaithfulSMul R k]
local notation "E" => WithI (K R 0)

/-- The two interpretation maps use the supplied root of negative one. -/
structure Fits (J : Interpretation E k n) (j : k) : Prop where
  scalar (u : K E 0) : J.scalar u = Model.constantHom k (project 0 u).re +
    j * Model.constantHom k (project 0 u).im
  field (u : K E n) : J.field u = val k (project n u).re +
    Model.C k n j * val k (project n u).im

/-- The interpretation from the chosen root satisfies both coefficient identities. -/
theorem fits_quadraticModelHom (j : k) (hj : j^2 = -1) :
    letI := (quadraticModelHom (R := R) k j hj).toAlgebra
    Fits (Interpretation.standard (S := E) (n := n) k) j := by
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  exact ⟨constantHom_project k (quadraticConstantHom_compatible k j hj) j
      (quadraticI_value k j hj),
    val_project k (quadraticConstantHom_compatible k j hj) j (quadraticI_value k j hj) n⟩

private theorem project_zero (m : ℕ) : project m (0 : K E m) = 0 := by
  change coordinatesEquiv (R := R) m 0 = 0
  exact map_zero _

private theorem poly_parts {A B V : Type} [Field A] [DecidableEq A] [Field B] [DecidableEq B]
    [Field V] (u v : A → B) (hu : u 0 = 0) (hv : v 0 = 0) (g : B →+* V)
    (f : A →+* V) (j : V) (h : ∀ a, f a = g (u a)+j*g (v a)) (p : Poly A) :
    Step.modelPoly f p = Step.modelPoly g (p.map u) + C j * Step.modelPoly g (p.map v) := by
  ext d
  simp [Poly.coeff_map _ hu,Poly.coeff_map _ hv,h]

theorem Fits.modulus {J : Interpretation E k n} {j : k} (H : Fits J j) (s : RootSum E n) :
    J.modulus s = Step.modelPoly (Model.constantHom k) (s.modulus.map (fun a => (project 0 a).re)) +
      C j * Step.modelPoly (Model.constantHom k) (s.modulus.map (fun a => (project 0 a).im)) := by
  exact poly_parts _ _ (by simp [project_zero]) (by simp [project_zero]) _ _ _ H.scalar _

theorem Fits.argument {J : Interpretation E k n} {j : k} (H : Fits J j) (s : RootSum E n) (z : k) :
    let e := Step.atRoot (val k) (Model.C k n z)
    J.argument s z = e (s.arg.map (fun a => (project n a).re)) +
      Model.C k n j * e (s.arg.map (fun a => (project n a).im)) := by
  have he := poly_parts _ _ (by simp [project_zero]) (by simp [project_zero])
    (val k) J.field _ H.field s.arg
  calc
    J.argument s z = (Step.modelPoly J.field s.arg).eval (Model.C k n z) := rfl
    _ = _ := by rw [he,eval_add,eval_mul,eval_C]; rfl

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
