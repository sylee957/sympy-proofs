module

public import SympyProofs.Gosper.Polynomiality

/-! # Rational-function formulation of Gosper's theorem -/

@[expose] public section
noncomputable section

namespace Gosper

open Polynomial

variable {K : Type*} [Field K]

/-- Translation of rational functions, extending polynomial translation. -/
def rationalShift (a : K) : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom ((algebraMap K[X] (RatFunc K)).comp (taylorAlgHom a).toRingHom)
    (by
      intro p hp
      change algebraMap K[X] (RatFunc K) (taylor a p) ∈ nonZeroDivisors _
      rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
      exact fun h => hp ((taylor_eq_zero a p).mp
        ((IsFractionRing.injective K[X] (RatFunc K)) (by simpa using h))))

@[simp] theorem rationalShift_polynomial (a : K) (p : K[X]) :
    rationalShift a (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (taylor a p) :=
  RatFunc.liftRingHom_algebraMap _ _ _

theorem rationalShift_fraction (a : K) (f : RatFunc K) :
    rationalShift a f =
      algebraMap K[X] (RatFunc K) (taylor a f.num) /
        algebraMap K[X] (RatFunc K) (taylor a f.denom) := by
  conv_lhs => rw [← f.num_div_denom]
  rw [map_div₀, rationalShift_polynomial, rationalShift_polynomial]

/-- Equation (8) in the rational-function field. -/
def RationalSolution (p q r : K[X]) (f : RatFunc K) : Prop :=
  algebraMap K[X] (RatFunc K) p =
    algebraMap K[X] (RatFunc K) (taylor 1 q) * f -
      algebraMap K[X] (RatFunc K) r * rationalShift (-1) f

theorem rationalSolution_polynomial_iff (p q r f : K[X]) :
    RationalSolution p q r (algebraMap K[X] (RatFunc K) f) ↔ operator q r f = p := by
  unfold RationalSolution
  rw [rationalShift_polynomial]
  rw [← map_mul, ← map_mul, ← map_sub]
  exact ⟨fun h => ((IsFractionRing.injective K[X] (RatFunc K)) h).symm,
    fun h => congrArg (algebraMap K[X] (RatFunc K)) h.symm⟩

/-- Equation (8') follows from equation (8) for the canonical reduced fraction. -/
theorem RationalSolution.clear_denominators {p q r : K[X]} {f : RatFunc K}
    (h : RationalSolution p q r f) :
    f.denom * taylor (-1) f.denom * p =
      f.num * taylor (-1) f.denom * taylor 1 q -
        f.denom * taylor (-1) f.num * r := by
  let ι := algebraMap K[X] (RatFunc K)
  have hd : ι f.denom ≠ 0 := by
    exact fun h => f.denom_ne_zero ((IsFractionRing.injective K[X] (RatFunc K))
      (by simpa [ι] using h))
  have hs : ι (taylor (-1) f.denom) ≠ 0 := by
    exact fun h => f.denom_ne_zero ((taylor_eq_zero (-1) f.denom).mp
      ((IsFractionRing.injective K[X] (RatFunc K)) (by simpa [ι] using h)))
  unfold RationalSolution at h
  rw [rationalShift_fraction] at h
  nth_rw 1 [← f.num_div_denom] at h
  change ι p = ι (taylor 1 q) * (ι f.num / ι f.denom) -
    ι r * (ι (taylor (-1) f.num) / ι (taylor (-1) f.denom)) at h
  apply IsFractionRing.injective K[X] (RatFunc K)
  simp only [map_mul, map_sub]
  change ι f.denom * ι (taylor (-1) f.denom) * ι p =
    ι f.num * ι (taylor (-1) f.denom) * ι (taylor 1 q) -
      ι f.denom * ι (taylor (-1) f.num) * ι r
  field_simp at h
  linear_combination h

/-- The central theorem of the paper: a rational solution of the normalized
Gosper equation is a polynomial. -/
theorem rational_solution_is_polynomial [CharZero K] (p q r : K[X])
    (hqr : ShiftCoprime q r) (f : RatFunc K) (hf : RationalSolution p q r f) :
    ∃ F : K[X], algebraMap K[X] (RatFunc K) F = f := by
  have hu := denominator_isUnit p q r f.num f.denom f.denom_ne_zero
    f.isCoprime_num_denom hqr hf.clear_denominators
  obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨C c⁻¹ * f.num, ?_⟩
  conv_rhs => rw [← f.num_div_denom, ← hc]
  simp [map_mul, div_eq_mul_inv, RatFunc.algebraMap_C, mul_comm]

/-- Completeness of polynomial certificates for the normalized rational equation. -/
theorem rational_solution_iff_polynomial [CharZero K] (p q r : K[X])
    (hqr : ShiftCoprime q r) :
    (∃ f : RatFunc K, RationalSolution p q r f) ↔
      ∃ F : K[X], operator q r F = p := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨F, rfl⟩ := rational_solution_is_polynomial p q r hqr f hf
    exact ⟨F, (rationalSolution_polynomial_iff p q r F).mp hf⟩
  · rintro ⟨F, hF⟩
    exact ⟨algebraMap K[X] (RatFunc K) F,
      (rationalSolution_polynomial_iff p q r F).mpr hF⟩

end Gosper
