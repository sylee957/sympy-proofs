module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Liouville
public import SympyProofs.Calculus.Antiderivative.Proof.Answer

/-! The reduced Laurent numerator represents a field derivative and one lower-field term. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

theorem Tower.Elementary.zero (t : Tower R n) : t.Elementary k 0 :=
  ⟨0, [], by simp⟩

theorem Tower.Elementary.derivative_add {t : Tower R n} {x : M k n}
    (h : t.Elementary k x)
    (y : M k n) : t.Elementary k (t.modelD k y + x) := by
  obtain ⟨a,logs,rfl⟩ := h
  exact ⟨y+a,logs,by rw [map_add, add_assoc]⟩

theorem Tower.Elementary.includeVars {t : Tower R n} {x : M k n} (h : t.Elementary k x)
    (g : ReducedGen (K R n)) : (t.step g).Elementary k (Model.includeVars (Nat.le_succ n) x) := by
  obtain ⟨y,logs,h⟩ := h
  let f := Model.includeVars (R := k) (Nat.le_succ n)
  refine ⟨f y, logs.map fun (c,u) => (c, f u), ?_⟩
  rw [h, map_add, map_list_sum, List.map_map, List.map_map, Tower.modelD_includeVars]
  simp [f, Function.comp_def]

namespace Elementary

/-- A primitive step uses only polynomial powers; exponentials may use any Laurent shift. -/
def LawfulShift (g : ReducedGen (K R n)) (s : ℕ) : Prop :=
  match g with | .prim _ => s = 0 | .exp _ => True

/-- A Laurent numerator in the multivariate model of the tower. -/
noncomputable def laurentValue (s : ℕ) (p : Polynomial (M k n)) : M k (n+1) :=
  (Model.stepEquiv k n).symm (algebraMap (Polynomial (M k n)) (RatFunc (M k n)) p / RatFunc.X ^ s)

theorem laurentValue_add (s : ℕ) (p q : Polynomial (M k n)) :
    laurentValue k s (p+q) = laurentValue k s p + laurentValue k s q := by
  simp [laurentValue, add_div]

theorem laurentValue_monomial (s : ℕ) (c : M k n) :
    laurentValue k s (monomial s c) = Model.includeVars (Nat.le_succ n) c := by
  apply (Model.stepEquiv k n).injective
  simp [laurentValue, ← C_mul_X_pow_eq_monomial, Model.stepEquiv_includeVars,
    pow_ne_zero s (RatFunc.X_ne_zero : (RatFunc.X : RatFunc (M k n)) ≠ 0)]

/-- Formally differentiating a Laurent polynomial gives its computed numerator operator. -/
theorem deriv_laurentValue (t : Tower R n) (g : ReducedGen (K R n)) (s : ℕ)
    (hs : LawfulShift g s)
    (q : Polynomial (M k n)) :
    (t.step g).modelD k (laurentValue k s q) = laurentValue k s (laurentOp k t g s q) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (RatFunc (M k n)) :=
    ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k g)⟩
  let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) :=
    ⟨fun a => Model.extendVariable_C _ _ a⟩
  apply (Model.stepEquiv k n).injective
  rw [Tower.stepEquiv_modelD]
  simp only [laurentValue, RingEquiv.apply_symm_apply]
  cases g with
  | prim b =>
    obtain rfl : s = 0 := hs
    simp only [pow_zero, div_one]
    rw [Model.extendVariable, Extension.extend_poly]
    congr 1
    simp [laurentOp, Solve.operator, Solve.modelPoly, Tower.polyDerModel]
  | exp u =>
    let du := val k (t.D u)
    have hx : Model.extendVariable (t.modelD k) (t.modelVelocity k (.exp u)) RatFunc.X =
        RatFunc.C du * RatFunc.X := by simp [du, Tower.modelVelocity]
    let _ : Differential (RatFunc (M k n)) :=
      ⟨Model.extendVariable (t.modelD k) (t.modelVelocity k (.exp u))⟩
    let _ : DifferentialAlgebra (M k n) (RatFunc (M k n)) :=
      ⟨fun a => Model.extendVariable_C _ _ a⟩
    have he := Extension.LiouvilleForm.deriv_div_X_pow (a := du) hx q s
    refine he.trans ?_
    congr 2
    change Extension.affine du 0 q - C _ * q =
      Solve.modelPoly k (1 : Poly (K R n)) * (t.polyDerModel k (.exp u)) q +
      Solve.modelPoly k (Poly.C (-(s : K R n)*(Gen.velocity (.exp u) t.D).coeff 1)) * q
    have ht : (Gen.velocity (.exp u) t.D).coeff 1 = t.D u := by
      simp [Gen.velocity, ← Poly.coeff_equiv]
    rw [ht]
    simp only [Solve.modelPoly, map_one, Polynomial.map_one, one_mul, Poly.equiv_C, map_C]
    simp [Tower.polyDerModel, Tower.modelVelocity, Extension.affine, du, sub_eq_add_neg]
    exact (neg_mul ((s : Polynomial (M k n)) * C (t.modelD k (val k u))) q).symm

/-- A lower elementary residual and its computed polynomial correction give a Liouville
form for the original Laurent integrand. -/
theorem elementary_of_correction (t : Tower R n) (g : ReducedGen (K R n)) (s : ℕ)
    (hs : LawfulShift g s)
    (p q : Polynomial (M k n)) (r : M k n) (he : t.Elementary k r)
    (hp : p = laurentOp k t g s q + monomial s r) :
    (t.step g).Elementary k (laurentValue k s p) := by
  rw [hp, laurentValue_add, ← deriv_laurentValue k t g s hs, laurentValue_monomial]
  exact (he.includeVars k g).derivative_add k _

end Elementary

end SympyProofs.Calculus.Antiderivative
