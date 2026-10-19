module

public import SympyProofs.Binomial.UniqueExteensions.Interpolation
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Polynomial.Roots

/-!
# Uniqueness of the circle integral with a fixed Fourier spectrum

`AgreesWithSympyIntegers` specifies the integer data. The characterization
supplements it with two independent conditions:

* every integer-lower slice is a polynomial in the upper argument;
* after multiplication by `exp (w * log r)`, every lower slice is a Fourier integral
  of a continuous density on the fixed angle interval `[0, 2π]`.

The density is arbitrary in the specification: its values are not prescribed.
Polynomial uniqueness first extends integer-pair agreement to integer-lower
agreement. Completeness of the Fourier basis then determines the density, and
hence the values at every complex lower argument.

For each fixed `r`, `circleIntegralChoose r` is the unique function satisfying these
conditions. Joint entire analyticity and Pascal follow from this characterization;
neither needs to be assumed. The radius and angle interval are normalization choices, not a
claim that integer data or Pascal intrinsically single out one interpolation.
This is a Fourier representation criterion; equivalence with a growth-only
Paley-Wiener condition is not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace SympyBinomial

/-- The angle circle used by the entire interpolation. -/
abbrev InterpolationCircle := AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Evaluate a circle density at a complex frequency, with fixed radial weight. -/
def circleTransform (r : InterpolationRadius) (g : C(InterpolationCircle, ℂ))
    (w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ in 0..2 * Real.pi,
    g (t : InterpolationCircle) *
      Complex.exp (-w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))

/-- A lower slice has the specified spectrum if some continuous circle density
represents it. The density is not fixed by this predicate. -/
def HasCircleSpectrum (r : InterpolationRadius) (f : ℂ → ℂ) : Prop :=
  ∃ g : C(InterpolationCircle, ℂ), ∀ w, f w = circleTransform r g w

private theorem fourier_angle (k : ℤ) (t : ℝ) :
    fourier k (t : InterpolationCircle) =
      Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Integer frequencies recover the ordinary Fourier coefficients, up to a
nonzero radial weight. -/
theorem circleTransform_int (r : InterpolationRadius)
    (g : C(InterpolationCircle, ℂ)) (k : ℤ) :
    circleTransform r g (k : ℂ) =
      Complex.exp (-(k : ℂ) * Complex.log (r : ℂ)) * fourierCoeff g k := by
  rw [fourierCoeff_eq_intervalIntegral g k 0]
  simp only [zero_add, one_div, smul_eq_mul, Complex.real_smul]
  unfold circleTransform
  have hi : ∀ t : ℝ,
      g (t : InterpolationCircle) *
          Complex.exp (-(k : ℂ) * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.exp (-(k : ℂ) * Complex.log (r : ℂ)) *
          (fourier (-k) (t : InterpolationCircle) * g (t : InterpolationCircle)) := by
    intro t
    rw [mul_add, Complex.exp_add, fourier_angle]
    push_cast
    simp only [mul_assoc]
    ring
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul]
  push_cast
  ring

private theorem continuousMap_eq_of_fourierCoeff_eq
    {g h : C(InterpolationCircle, ℂ)} (heq : ∀ k, fourierCoeff g k = fourierCoeff h k) :
    g = h := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  apply fourierBasis.repr.injective
  ext k
  rw [fourierBasis_repr, fourierBasis_repr]
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle g),
    fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle h)]
  exact heq k

/-- Integer samples determine every complex value within the fixed spectrum. -/
theorem HasCircleSpectrum.eq_of_int_eq {r : InterpolationRadius} {f h : ℂ → ℂ}
    (hf : HasCircleSpectrum r f) (hh : HasCircleSpectrum r h)
    (heq : ∀ k : ℤ, f (k : ℂ) = h (k : ℂ)) : f = h := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨q, hq⟩ := hh
  have hd : g = q := by
    apply continuousMap_eq_of_fourierCoeff_eq
    intro k
    have hi := heq k
    rw [hg, hq, circleTransform_int, circleTransform_int] at hi
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hi
  funext w
  rw [hg, hq, hd]

private theorem exists_polynomial_choose (k : ℤ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, choose z k = p.eval z := by
  by_cases hk : k < 0
  · exact ⟨0, fun z => by simp [choose_of_neg z hk]⟩
  · refine ⟨(descPochhammer ℂ k.toNat) * Polynomial.C ((k.toNat.factorial : ℂ)⁻¹), ?_⟩
    intro z
    rw [← Int.toNat_of_nonneg (le_of_not_gt hk), choose_eq_descPochhammer]
    simp [div_eq_mul_inv, max_eq_left (le_of_not_gt hk)]

/-- Polynomiality promotes integer-pair agreement to agreement on each whole
integer-lower slice. Neither analyticity nor Pascal nor a degree bound is assumed. -/
theorem AgreesWithSympyIntegers.int_lower_eq_of_polynomial {F : ℂ → ℂ → ℂ}
    (hF : AgreesWithSympyIntegers F)
    (hpoly : ∀ k : ℤ, ∃ p : Polynomial ℂ, ∀ z, F z (k : ℂ) = p.eval z)
    (z : ℂ) (k : ℤ) : F z (k : ℂ) = choose z k := by
  obtain ⟨p, hp⟩ := hpoly k
  obtain ⟨q, hq⟩ := exists_polynomial_choose k
  have hpq : p = q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Int.cast_injective (α := ℂ))).mono
    rintro _ ⟨n, rfl⟩
    change p.eval (n : ℂ) = q.eval (n : ℂ)
    rw [← hp, ← hq, hF, intCast_choose]
  rw [hp, hq, hpq]

/-- The polynomial criterion applied to the existing entire binomial class. -/
theorem IsEntireBinomial.int_lower_eq_of_polynomial {F : ℂ → ℂ → ℂ}
    (hF : IsEntireBinomial F)
    (hpoly : ∀ k : ℤ, ∃ p : Polynomial ℂ, ∀ z, F z (k : ℂ) = p.eval z)
    (z : ℂ) (k : ℤ) : F z (k : ℂ) = choose z k :=
  hF.intCast_intCast.int_lower_eq_of_polynomial hpoly z k

/-- The fixed-circle characterization of the integer data. Joint entire
analyticity and Pascal are consequences, proved by `toIsEntireBinomial`. -/
structure IsCircleBinomial (r : InterpolationRadius) (F : ℂ → ℂ → ℂ) : Prop where
  intCast_intCast : AgreesWithSympyIntegers F
  polynomial_upper : ∀ k : ℤ, ∃ p : Polynomial ℂ, ∀ z, F z (k : ℂ) = p.eval z
  circle_spectrum : ∀ z, HasCircleSpectrum r (F z)

/-- Two normalized entire interpolations with the same radius coincide. -/
theorem IsCircleBinomial.eq {r : InterpolationRadius} {F G : ℂ → ℂ → ℂ}
    (hF : IsCircleBinomial r F) (hG : IsCircleBinomial r G) : F = G := by
  funext z
  apply (hF.circle_spectrum z).eq_of_int_eq (hG.circle_spectrum z)
  intro k
  rw [hF.intCast_intCast.int_lower_eq_of_polynomial hF.polynomial_upper,
    hG.intCast_intCast.int_lower_eq_of_polynomial hG.polynomial_upper]

private def binomialCircleDensity (r : InterpolationRadius) (z : ℂ) :
    C(InterpolationCircle, ℂ) where
  toFun t := Complex.exp (z * Complex.log (1 + (r : ℂ) * fourier 1 t))
  continuous_toFun := by
    apply Continuous.cexp
    apply continuous_const.mul
    apply Continuous.clog
    · exact continuous_const.add (continuous_const.mul (fourier 1).continuous)
    · intro t
      apply Complex.mem_slitPlane_of_norm_lt_one
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos r.property.1] using r.property.2

/-- The defining integral has a continuous circle density for every upper argument. -/
theorem hasCircleSpectrum_circleIntegralChoose (r : InterpolationRadius) (z : ℂ) :
    HasCircleSpectrum r (circleIntegralChoose r z) := by
  refine ⟨binomialCircleDensity r z, fun w => ?_⟩
  unfold circleIntegralChoose circleTransform
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)) =
    Complex.exp (z * Complex.log (1 + (r : ℂ) * fourier 1 (t : InterpolationCircle))) * _
  rw [fourier_angle, Int.cast_one, one_mul, circleMap_zero,
    sub_eq_add_neg, Complex.exp_add, neg_mul]

/-- Existence: the proposed uniqueness conditions are satisfied by the integral
construction, so the specification is not vacuous. -/
theorem isCircleBinomial_circleIntegralChoose (r : InterpolationRadius) :
    IsCircleBinomial r (circleIntegralChoose r) where
  intCast_intCast := circleIntegralChoose_intCast_intCast r
  polynomial_upper := by
    intro k
    obtain ⟨p, hp⟩ := exists_polynomial_choose k
    exact ⟨p, fun z => (circleIntegralChoose_int_eq_choose r z k).trans (hp z)⟩
  circle_spectrum := hasCircleSpectrum_circleIntegralChoose r

/-- The normalized class consists of exactly the chosen integral interpolation. -/
theorem isCircleBinomial_iff (r : InterpolationRadius) (F : ℂ → ℂ → ℂ) :
    IsCircleBinomial r F ↔ F = circleIntegralChoose r := by
  constructor
  · intro hF
    exact hF.eq (isCircleBinomial_circleIntegralChoose r)
  · rintro rfl
    exact isCircleBinomial_circleIntegralChoose r

/-- The unique extension is jointly entire, matches every SymPy integer pair,
and satisfies complex Pascal. These properties are derived from the criterion. -/
theorem IsCircleBinomial.toIsEntireBinomial {r : InterpolationRadius}
    {F : ℂ → ℂ → ℂ} (hF : IsCircleBinomial r F) : IsEntireBinomial F := by
  rw [(isCircleBinomial_iff r F).mp hF]
  exact isEntireBinomial_circleIntegralChoose r

/-- There exists exactly one normalized entire binomial for each chosen radius. -/
theorem existsUnique_isCircleBinomial (r : InterpolationRadius) :
    ∃! F : ℂ → ℂ → ℂ, IsCircleBinomial r F :=
  ⟨circleIntegralChoose r, isCircleBinomial_circleIntegralChoose r,
    fun _ hF => (isCircleBinomial_iff r _).mp hF⟩

end SympyBinomial
