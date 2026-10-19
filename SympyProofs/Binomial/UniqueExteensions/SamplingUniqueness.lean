module

public import SympyProofs.Binomial.UniqueExteensions.CenteredCircle
public import SympyProofs.Binomial.UniqueExteensions.CircleUniqueness

/-!
# Uniqueness of the centered extension by square-integrable sampling

Fix `0 < r < 1`. Require integer-pair agreement, polynomial integer-lower
slices, and the following independent function-space condition: for each `z`,
`w ↦ exp (w * log r) * F z w` is the Fourier transform of some square-integrable
density supported on `[-π,π]`. The density is arbitrary, not prescribed to be
the binomial density. No continuity of the density is required.

Integer samples give all Fourier coefficients of this density. Completeness
of the Fourier basis determines it almost everywhere, hence determines every
complex value of the transform. `existsUnique_isSampledBinomial` proves both
existence and uniqueness, with witness `centeredCircleChoose r`. Joint entire
analyticity, all integer-lower slices, and complex Pascal are consequences.

The extra condition has two parts: a fixed bandwidth and finite `L²` norm.
The latter matters at the critical bandwidth: `sin (πw)` has type `π` and
vanishes on all integers, but is not in `L²(ℝ)`. Requiring a type strictly below
`π` instead would exclude even the needed cardinal slice at upper argument zero.

The radial weight also matters. Without damping (`r=1`), the lower samples at
upper argument `-1` are `(-1)^k` for `k ≥ 0`, which are not square-summable and
therefore cannot be samples of an `L²` transform with this bandwidth. For each
`r<1`, the weighted samples are `r^k * (-1)^k`, which are square-summable.
This explanation uses classical sampling theory; the formal existence proof
below instead constructs the density directly.

Classically, the Paley-Wiener theorem gives an equivalent formulation: the
weighted lower slice is entire of exponential type at most `π` and belongs to
`L²(ℝ)`. This equivalence is NOT formalized here; the Lean specification uses
the square-integrable Fourier representation directly. See A. P. Austin,
*Some New Results on and Applications of Interpolation in Numerical Computation*,
§3.2.3-4, https://www.mcs.anl.gov/~aaustin/pubs/DPhilThesis.pdf .

The bandwidth, centered interval, and radius are normalization choices. This
does not claim a parameter-free canonical extension.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace SympyBinomial

/-- A Fourier transform over the centered angle interval, with radial weight. -/
def centeredTransform (r : InterpolationRadius) (g : InterpolationCircle → ℂ)
    (w : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ in -Real.pi..Real.pi,
    g (t : InterpolationCircle) *
      Complex.exp (-w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I))

/-- The weighted slice has bandwidth `π` with a square-integrable density.
The witness is arbitrary and only required to be square-integrable. -/
def HasCenteredSpectrum (r : InterpolationRadius) (f : ℂ → ℂ) : Prop :=
  ∃ g : InterpolationCircle → ℂ, MemLp g 2 AddCircle.haarAddCircle ∧
    ∀ w, f w = centeredTransform r g w

private theorem fourier_angle (k : ℤ) (t : ℝ) :
    fourier k (t : InterpolationCircle) =
      Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Integer samples are Fourier coefficients multiplied by a nonzero weight. -/
theorem centeredTransform_int (r : InterpolationRadius)
    (g : InterpolationCircle → ℂ) (k : ℤ) :
    centeredTransform r g (k : ℂ) =
      Complex.exp (-(k : ℂ) * Complex.log (r : ℂ)) * fourierCoeff g k := by
  rw [fourierCoeff_eq_intervalIntegral g k (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  simp only [one_div, smul_eq_mul, Complex.real_smul]
  unfold centeredTransform
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

/-- Changing a density on a null set does not change its complex transform. -/
theorem centeredTransform_congr_ae (r : InterpolationRadius)
    {g h : InterpolationCircle → ℂ} (heq : g =ᵐ[AddCircle.haarAddCircle] h)
    (w : ℂ) : centeredTransform r g w = centeredTransform r h w := by
  have hv : g =ᵐ[volume] h := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure heq _
  have hi := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).quasiMeasurePreserving.ae hv
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hi
  unfold centeredTransform
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by linarith [Real.pi_pos])]
  filter_upwards [hi] with t ht
  rw [ht]

/-- Sampling uniqueness in the weighted, centered square-integrable spectrum. -/
theorem HasCenteredSpectrum.eq_of_int_eq {r : InterpolationRadius} {f h : ℂ → ℂ}
    (hf : HasCenteredSpectrum r f) (hh : HasCenteredSpectrum r h)
    (heq : ∀ k : ℤ, f (k : ℂ) = h (k : ℂ)) : f = h := by
  obtain ⟨g, hgLp, hg⟩ := hf
  obtain ⟨q, hqLp, hq⟩ := hh
  have hcoeff : ∀ k, fourierCoeff g k = fourierCoeff q k := by
    intro k
    have hi := heq k
    rw [hg, hq, centeredTransform_int, centeredTransform_int] at hi
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hi
  have hd : hgLp.toLp g = hqLp.toLp q := by
    apply fourierBasis.repr.injective
    ext k
    rw [fourierBasis_repr, fourierBasis_repr,
      fourierCoeff_congr_ae hgLp.coeFn_toLp, fourierCoeff_congr_ae hqLp.coeFn_toLp]
    exact hcoeff k
  have hae := (MemLp.toLp_eq_toLp_iff hgLp hqLp).mp hd
  funext w
  rw [hg, hq]
  exact centeredTransform_congr_ae r hae w

/-- A specification from integer data and function-space constraints only. -/
structure IsSampledBinomial (r : InterpolationRadius) (F : ℂ → ℂ → ℂ) : Prop where
  intCast_intCast : AgreesWithSympyIntegers F
  polynomial_upper : ∀ k : ℤ, ∃ p : Polynomial ℂ, ∀ z, F z (k : ℂ) = p.eval z
  centered_spectrum : ∀ z, HasCenteredSpectrum r (F z)

theorem IsSampledBinomial.eq {r : InterpolationRadius} {F G : ℂ → ℂ → ℂ}
    (hF : IsSampledBinomial r F) (hG : IsSampledBinomial r G) : F = G := by
  funext z
  apply (hF.centered_spectrum z).eq_of_int_eq (hG.centered_spectrum z)
  intro k
  rw [hF.intCast_intCast.int_lower_eq_of_polynomial hF.polynomial_upper,
    hG.intCast_intCast.int_lower_eq_of_polynomial hG.polynomial_upper]

private def centeredBinomialDensity (r : InterpolationRadius) (z : ℂ) :
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

theorem hasCenteredSpectrum_centeredCircleChoose (r : InterpolationRadius) (z : ℂ) :
    HasCenteredSpectrum r (centeredCircleChoose r z) := by
  refine ⟨centeredBinomialDensity r z,
    ContinuousMap.memLp AddCircle.haarAddCircle ℂ (centeredBinomialDensity r z), fun w => ?_⟩
  unfold centeredCircleChoose angleCircleChoose centeredTransform
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change Complex.exp (z * Complex.log (1 + circleMap 0 r t) -
      w * (Complex.log (r : ℂ) + (t : ℂ) * Complex.I)) =
    Complex.exp (z * Complex.log (1 + (r : ℂ) * fourier 1 (t : InterpolationCircle))) * _
  rw [fourier_angle, Int.cast_one, one_mul, circleMap_zero,
    sub_eq_add_neg, Complex.exp_add, neg_mul]

/-- Existence in the specified function space, not just an at-most-one result. -/
theorem isSampledBinomial_centeredCircleChoose (r : InterpolationRadius) :
    IsSampledBinomial r (centeredCircleChoose r) where
  intCast_intCast := centeredCircleChoose_intCast_intCast r
  polynomial_upper := by
    intro k
    obtain ⟨p, hp⟩ := (isCircleBinomial_circleIntegralChoose r).polynomial_upper k
    refine ⟨p, fun z => ?_⟩
    rw [centeredCircleChoose_int_eq_choose,
      ← circleIntegralChoose_int_eq_choose r z k, hp]
  centered_spectrum := hasCenteredSpectrum_centeredCircleChoose r

theorem isSampledBinomial_iff (r : InterpolationRadius) (F : ℂ → ℂ → ℂ) :
    IsSampledBinomial r F ↔ F = centeredCircleChoose r := by
  constructor
  · intro hF
    exact hF.eq (isSampledBinomial_centeredCircleChoose r)
  · rintro rfl
    exact isSampledBinomial_centeredCircleChoose r

/-- Entire analyticity and Pascal are derived, not imposed in the specification. -/
theorem IsSampledBinomial.toIsEntireBinomial {r : InterpolationRadius}
    {F : ℂ → ℂ → ℂ} (hF : IsSampledBinomial r F) : IsEntireBinomial F := by
  rw [(isSampledBinomial_iff r F).mp hF]
  exact isEntireBinomial_centeredCircleChoose r

/-- There is exactly one extension with the fixed weighted centered spectrum. -/
theorem existsUnique_isSampledBinomial (r : InterpolationRadius) :
    ∃! F : ℂ → ℂ → ℂ, IsSampledBinomial r F :=
  ⟨centeredCircleChoose r, isSampledBinomial_centeredCircleChoose r,
    fun _ hF => (isSampledBinomial_iff r _).mp hF⟩

end SympyBinomial
