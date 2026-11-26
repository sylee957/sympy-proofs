module

public import SympyProofs.Calculus.Antiderivative.Spec.Gaussian
public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricConstants
public import SympyProofs.Calculus.Antiderivative.Spec.Level

/-! The ground embeddings used when compiling rational and quadratic tangent towers. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Include a coefficient in the flat rational-function field at any height. -/
def K.CRingHom (n : ℕ) : R →+* K R n where
  toFun := K.C
  map_zero' := K.equiv.injective (by simp)
  map_one' := K.equiv.injective (by simp)
  map_mul' a b := K.equiv.injective (by simp)
  map_add' a b := K.equiv.injective (by simp)

namespace Trigonometric

/-- The compiler's executable inclusion of rational constants is a field embedding. -/
noncomputable def gaussianConstantHom : K ℤ 0 →+* K Gaussian 0 :=
  (K.CRingHom 0).comp ((Rat.castHom Gaussian).comp (K.constantsEquiv ℚ).toRingHom)

theorem gaussianConstantHom_apply (a : K ℤ 0) : gaussianConstantHom a = gaussianConstant a := rfl

/-- Interpreting a rational constant in either presentation gives the same model scalar. -/
theorem gaussianConstantHom_compatible (k : Type) [Field k] [CharZero k]
    [Algebra Gaussian k] [FaithfulSMul Gaussian k] (a : K ℤ 0) :
    Model.constantHom k (gaussianConstantHom a) = Model.constantHom k a := by
  obtain ⟨q,rfl⟩ : ∃ q : ℚ, (q : K ℤ 0) = a := by
    refine ⟨K.toConstants ℚ a,(K.constantsEquiv ℚ).injective ?_⟩
    rw [map_ratCast]
    rfl
  simp

/-- The constant used in rational-input tangent compilation squares to negative one. -/
theorem gaussianI_sq : (K.C Gaussian.I : K Gaussian 0) ^ 2 = -1 := by
  change (K.CRingHom 0 Gaussian.I) ^ 2 = -1
  rw [← map_pow, Gaussian.I_sq, map_neg, map_one]

/-- The ground embedding of an arbitrary coefficient field into its quadratic extension. -/
noncomputable def quadraticConstantHom [Fact (¬ IsSquare (-1 : K R 0))] :
    K R 0 →+* K (WithI (K R 0)) 0 :=
  (K.CRingHom 0).comp (algebraMap (K R 0) (WithI (K R 0)))

theorem quadraticConstantHom_apply [Fact (¬ IsSquare (-1 : K R 0))] (a : K R 0) :
    quadraticConstantHom a = K.C (QuadraticAlgebra.C a : WithI (K R 0)) := rfl

/-- The compiler's adjoined imaginary unit has its defining quadratic relation. -/
theorem quadraticI_sq [Fact (¬ IsSquare (-1 : K R 0))] :
    (K.C (WithI.imaginary (K R 0)) : K (WithI (K R 0)) 0) ^ 2 = -1 := by
  change (K.CRingHom 0 (WithI.imaginary (K R 0))) ^ 2 = -1
  rw [← map_pow, WithI.imaginary_sq, map_neg, map_one]

end Trigonometric

end SympyProofs.Calculus.Antiderivative
