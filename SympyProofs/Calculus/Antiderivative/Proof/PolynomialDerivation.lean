module

public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.StepModel
public import SympyProofs.Calculus.Antiderivative.Spec.Split
public import SympyProofs.Calculus.Antiderivative.Program.Solve

/-! The derivative used by the executable Hermite and residue steps agrees with the
differential-field derivative on polynomials in the newest generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Tower

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

/-- The model polynomial derivation for the newest generator. -/
noncomputable def polyDerModel (t : Tower R n) (g : Gen (K R n)) :
    Derivation ℤ (M k n)[X] (M k n)[X] :=
  letI : Differential (M k n) := ⟨t.modelD k⟩
  Differential.implicitDeriv (t.modelVelocity k g)

theorem modelPoly_velocity (t : Tower R n) (g : Gen (K R n)) :
    Step.modelPoly (val k) (g.velocity t.D) = t.modelVelocity k g := by
  cases g <;> simp [Gen.velocity, modelVelocity, ← C_mul_X_pow_eq_monomial]

/-- The executable coefficient derivative and chain rule realize the model polynomial derivation. -/
theorem modelPoly_polyDer (t : Tower R n) (g : Gen (K R n)) (p : Poly (K R n)) :
    Step.modelPoly (val k) (Step.polyDer t.D (g.velocity t.D) p) =
      t.polyDerModel k g (Step.modelPoly (val k) p) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have hc : Step.modelPoly (val k) (p.map t.D) =
      Differential.mapCoeffs (Step.modelPoly (val k) p) := by
    ext i
    simp [Poly.coeff_map t.D (K.der_zero _)]
    rfl
  change _ = Differential.mapCoeffs _ + t.modelVelocity k g * (Step.modelPoly (val k) p).derivative
  rw [Step.polyDer, map_add, map_mul, hc, modelPoly_velocity]
  simp only [Step.modelPoly_apply, Poly.equiv_derivative, derivative_map]

/-- Adjoining a polynomial in the newest generator commutes with its model derivative. -/
theorem modelD_adjoinPoly (t : Tower R n) (g : Gen (K R n)) (p : (M k n)[X]) :
    let e := Model.stepEquiv k n
    let ι := algebraMap (M k n)[X] (RatFunc (M k n))
    (t.step g).modelD k (e.symm (ι p)) = e.symm (ι (t.polyDerModel k g p)) := by
  dsimp only
  apply (Model.stepEquiv k n).injective
  rw [stepEquiv_modelD, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact Extension.extend_poly (t.polyDerModel k g) p

/-- The field derivative of a computed polynomial is its computed derivative evaluated
in the same newest generator. -/
theorem modelD_joinPoly (t : Tower R n) (g : Gen (K R n)) (p : Poly (K R n)) :
    (t.step g).modelD k (val k (K.joinPoly p)) =
      val k (K.joinPoly (Step.polyDer t.D (g.velocity t.D) p)) := by
  have join (q : Poly (K R n)) : val k (K.joinPoly q) = (Model.stepEquiv k n).symm
      (algebraMap _ _ (Step.modelPoly (val k) q)) := by
    apply (Model.stepEquiv k n).injective
    rw [RingEquiv.apply_symm_apply]
    exact val_joinPoly k q
  rw [join, join, modelD_adjoinPoly, modelPoly_polyDer]

/-- The leading coefficient of a monic polynomial derivative in an affine generator is the
exponent times the linear coefficient in the generator velocity. -/
theorem degree_polyDerModel (t : Tower R n) (g : ReducedGen (K R n)) {p : (M k n)[X]}
    (hp : p.Monic) :
    (t.polyDerModel k g p -
      C ((p.natDegree : M k n) * val k ((g.velocity t.D).coeff 1)) * p).degree < p.degree := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let a := val k ((g.velocity t.D).coeff 1)
  let b := val k ((g.velocity t.D).coeff 0)
  have hv : t.modelVelocity k g = C a * X + C b := by
    have he (i : ℕ) : val k ((g.velocity t.D).coeff i) = (t.modelVelocity k g).coeff i := by
      rw [← modelPoly_velocity k t g]
      simp
    cases g <;> simp [a, b, he, modelVelocity]
  have ha : t.polyDerModel k g = Extension.affine a b := by rw [polyDerModel, hv]
  rw [ha, degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sub, coeff_C_mul, Extension.coeff_affine]
  rcases Nat.eq_or_lt_of_le hi with rfl | hl
  · rw [hp.coeff_natDegree, coeff_natDegree_succ_eq_zero, Derivation.map_one_eq_zero]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt hl, coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    ring

end SympyProofs.Calculus.Antiderivative.Tower
