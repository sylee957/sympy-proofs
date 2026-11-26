module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! The rational function field on a finite set of generators and its last-variable presentation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The field of rational functions in the first `n` generators over the coefficients `k`. -/
abbrev M (k : Type*) [CommRing k] (n : ℕ) := FractionRing (MvPolynomial (Fin n) k)

namespace Model

open Polynomial

variable (R : Type*) [CommRing R] [IsDomain R]

/-- Embed a fraction of polynomials into rational functions over the fraction field. -/
noncomputable def fractionsToRatFunc :
    FractionRing R[X] →+* RatFunc (FractionRing R) :=
  IsFractionRing.lift (g := (algebraMap (FractionRing R)[X] _).comp
    (mapRingHom (algebraMap R (FractionRing R))))
    ((RatFunc.algebraMap_injective _).comp (map_injective _ (IsFractionRing.injective R _)))

@[simp] theorem fractionsToRatFunc_poly (p : R[X]) :
    fractionsToRatFunc R (algebraMap R[X] _ p) =
      algebraMap (FractionRing R)[X] _ (p.map (algebraMap R _)) :=
  IsFractionRing.lift_algebraMap _ p

/-- Every rational function over the fraction field is a fraction over the original ring. -/
theorem fractionsToRatFunc_surjective : Function.Surjective (fractionsToRatFunc R) := by
  let f := fractionsToRatFunc R
  have hX : (RatFunc.X : RatFunc (FractionRing R)) ∈ f.fieldRange := by
    use algebraMap R[X] _ X
    simp [f]
  have hC (a : FractionRing R) : RatFunc.C a ∈ f.fieldRange := by
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective R a
    use algebraMap R[X] _ (C x) / algebraMap R[X] _ (C y)
    simp [f, map_div₀]
  have hP (p : (FractionRing R)[X]) : algebraMap _ (RatFunc _) p ∈ f.fieldRange := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using f.fieldRange.add_mem hp hq
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      exact f.fieldRange.mul_mem (hC a) (f.fieldRange.pow_mem hX i)
  intro z
  induction z using RatFunc.induction_on with
  | f p q _ => exact f.fieldRange.div_mem (hP p) (hP q)

/-- Adjoining fractions of coefficients leaves the one-variable fraction field unchanged. -/
noncomputable def fractionsRatFuncEquiv :
    FractionRing R[X] ≃+* RatFunc (FractionRing R) :=
  RingEquiv.ofBijective _ ⟨(fractionsToRatFunc R).injective, fractionsToRatFunc_surjective R⟩

variable (k : Type*) [CommRing k] (n : ℕ)

/-- Expand a polynomial in the last variable, preserving the indices of the earlier variables. -/
noncomputable def splitPolynomial :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X] :=
  (MvPolynomial.renameEquiv k (finRotate (n + 1))).trans (MvPolynomial.finSuccEquiv k n)

@[simp] theorem splitPolynomial_last :
    splitPolynomial k n (MvPolynomial.X (Fin.last n)) = X := by
  simp [splitPolynomial, MvPolynomial.renameEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem splitPolynomial_castSucc (i : Fin n) :
    splitPolynomial k n (MvPolynomial.X i.castSucc) = C (MvPolynomial.X i) := by
  have hi : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simp [splitPolynomial, MvPolynomial.renameEquiv, hi, MvPolynomial.finSuccEquiv_X_succ]

variable [IsDomain k]

/-- The newest generator is a rational-function variable over the field one level below. -/
noncomputable def stepEquiv : M k (n + 1) ≃+* RatFunc (M k n) :=
  (IsFractionRing.ringEquivOfRingEquiv (splitPolynomial k n).toRingEquiv).trans
    (fractionsRatFuncEquiv (MvPolynomial (Fin n) k))

/-- The last-variable presentation of any polynomial, with its coefficients in the lower field. -/
theorem stepEquiv_polynomial (p : MvPolynomial (Fin (n + 1)) k) :
    stepEquiv k n (algebraMap _ _ p) =
      algebraMap (M k n)[X] _ ((splitPolynomial k n p).map (algebraMap _ _)) := by
  rw [stepEquiv, RingEquiv.trans_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact fractionsToRatFunc_poly _ _

@[simp] theorem stepEquiv_last :
    stepEquiv k n (algebraMap (MvPolynomial _ k) _ (MvPolynomial.X (Fin.last n))) =
      RatFunc.X := by
  simp [stepEquiv_polynomial]

@[simp] theorem stepEquiv_castSucc (i : Fin n) :
    stepEquiv k n (algebraMap (MvPolynomial _ k) _ (MvPolynomial.X i.castSucc)) =
      RatFunc.C (algebraMap (MvPolynomial _ k) _ (MvPolynomial.X i)) := by
  simp [stepEquiv_polynomial]

end Model

end SympyProofs.Calculus.Antiderivative
