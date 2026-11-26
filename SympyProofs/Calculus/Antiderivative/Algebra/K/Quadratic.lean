module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Split
public import SympyProofs.Calculus.Antiderivative.Algebra.Gaussian
import Mathlib.Tactic.Linarith

/-! Negative one stays nonsquare in rational extensions of the original constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

namespace Trigonometric

/-- Comparing leading coefficients shows a square root of negative one in a rational
function field already gives one in its coefficient field. -/
theorem nonsquare_ratFunc {F : Type} [Field F] (hf : ¬ IsSquare (-1 : F)) :
    ¬ IsSquare (-1 : RatFunc F) := by
  rintro ⟨y,hy⟩
  let ι := algebraMap F[X] (RatFunc F)
  have hy' : ((ι y.num) / (ι y.denom)) ^ 2 = -1 := by
    rw [RatFunc.num_div_denom, pow_two]
    exact hy.symm
  have hd : ι y.denom ≠ 0 := RatFunc.algebraMap_ne_zero y.denom_ne_zero
  rw [div_pow, div_eq_iff (pow_ne_zero _ hd), neg_one_mul] at hy'
  have hs : y.num ^ 2 = -(y.denom ^ 2) := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_neg, map_pow] using hy'
  have hl := congrArg Polynomial.leadingCoeff hs
  rw [leadingCoeff_neg, leadingCoeff_pow, leadingCoeff_pow] at hl
  have hd' := leadingCoeff_ne_zero.mpr y.denom_ne_zero
  apply hf
  refine ⟨y.num.leadingCoeff / y.denom.leadingCoeff, ?_⟩
  rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero _ hd'), neg_one_mul, hl]

/-- Adding any number of independent rational-function parameters preserves the nonsquare. -/
theorem nonsquare_model (F : Type) [Field F] (hf : ¬ IsSquare (-1 : F)) (n : ℕ) :
    ¬ IsSquare (-1 : M F n) := by
  induction n with
  | zero =>
    rintro ⟨a,ha⟩
    apply hf
    exact ⟨_,by simpa using congrArg (K.modelConstantsEquiv (R := F) F) ha⟩
  | succ n ih =>
    rintro ⟨a,ha⟩
    apply nonsquare_ratFunc ih
    exact ⟨_,by simpa using congrArg (Model.stepEquiv F n) ha⟩

/-- The constant field of integer-coefficient towers is rational and lacks an imaginary unit. -/
instance : Fact (¬ IsSquare (-1 : K ℤ 0)) where
  out := by
    rintro ⟨a,ha⟩
    have h : (-1 : ℚ) = K.constantsEquiv ℚ a * K.constantsEquiv ℚ a := by
      simpa using congrArg (K.constantsEquiv ℚ) ha
    nlinarith [sq_nonneg (K.constantsEquiv ℚ a)]

/-- Height-zero fractions over a field preserve the same nonsquare. -/
instance {F : Type} [Field F] [DecidableEq F] [Fact (¬ IsSquare (-1 : F))] :
    Fact (¬ IsSquare (-1 : K F 0)) where
  out := by
    rintro ⟨a,ha⟩
    apply Fact.out (p := ¬ IsSquare (-1 : F))
    exact ⟨_,by simpa using congrArg (K.constantsEquiv F) ha⟩

/-- A known nonsquare needs no factorization to decide the tangent reduction. -/
instance {F : Type} [Field F] [h : Fact (¬ IsSquare (-1 : F))] :
    Decidable (IsSquare (-1 : F)) := .isFalse h.out

/-- The quadratic coefficient algebra contains its distinguished imaginary unit. -/
instance {F : Type} [Field F] : Decidable (IsSquare (-1 : WithI F)) :=
  .isTrue ⟨WithI.imaginary F, by simpa [pow_two] using (WithI.imaginary_sq (F := F)).symm⟩

/-- At height zero a coefficient field and its flat fractions give the same square decision. -/
instance {F : Type} [Field F] [DecidableEq F] [Decidable (IsSquare (-1 : F))] :
    Decidable (IsSquare (-1 : K F 0)) :=
  decidable_of_iff (IsSquare (-1 : F)) (by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨_, by simpa using congrArg (K.constantsEquiv (R := F) F).symm ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, by simpa using congrArg (K.constantsEquiv (R := F) F) ha⟩)

end Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Negative one is nonsquare at every height if it is nonsquare at height zero. -/
theorem K.nonsquare_at (h : ¬ IsSquare (-1 : K R 0)) (n : ℕ) : ¬ IsSquare (-1 : K R n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hM : ¬ IsSquare (-1 : M R n) := by
      rintro ⟨z,hz⟩
      exact ih ⟨K.equiv.symm z, by simpa using congrArg K.equiv.symm hz⟩
    rintro ⟨y,hy⟩
    let e := K.equiv.trans (Model.stepEquiv R n)
    exact Trigonometric.nonsquare_ratFunc hM ⟨e y, by simpa using congrArg e hy⟩

/-- The imported quadratic field instance is available at variable tower heights. -/
instance (priority := low) (n : ℕ) [Fact (¬ IsSquare (-1 : K R 0))] :
    Fact (¬ IsSquare (-1 : K R n)) := ⟨K.nonsquare_at Fact.out n⟩

/-- Apply a field embedding to both coordinates of a quadratic extension. -/
def WithI.map {F G : Type} [Field F] [Field G] (f : F →+* G) : WithI F →+* WithI G where
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := QuadraticAlgebra.ext f.map_one f.map_zero
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

end SympyProofs.Calculus.Antiderivative
