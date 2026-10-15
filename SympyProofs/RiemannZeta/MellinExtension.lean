import SympyProofs.RiemannZeta.ThetaKernel
import SympyProofs.RiemannZeta.RightHalfPlane

/-!
# Holomorphic extension obtained from the Gaussian Mellin transform

The general Mellin theorem supplies an entire regularized transform. The
Gamma recurrence cancels its apparent pole at zero. Agreement with the
original series is proved by interchanging the Gaussian sum and Mellin
integral in the original half-plane of absolute convergence.
-/

noncomputable section
namespace RiemannZeta

open Complex Filter Set
open scoped Topology

namespace Gaussian

def entirePart (s : ℂ) : ℂ := thetaPair.Λ₀ (s / 2) / 2

def completed (s : ℂ) : ℂ := thetaPair.Λ (s / 2) / 2

theorem differentiable_entirePart : Differentiable ℂ entirePart :=
  (thetaPair.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

theorem completed_eq (s : ℂ) :
    completed s = entirePart s - 1 / s - 1 / (1 - s) := by
  rw [completed, WeakFEPair.Λ, sub_div, sub_div]
  change entirePart s - (1 / (s / 2)) * 1 / 2 -
    (1 / ((1 / 2 : ℝ) - s / 2)) * 1 / 2 = _
  push_cast
  simp only [mul_one, div_div, div_mul_cancel₀ _ (two_ne_zero' ℂ)]
  rw [← sub_div, div_mul_cancel₀ _ (two_ne_zero' ℂ)]

theorem completed_eq_mellin {s : ℂ} (hs : 1 < s.re) :
    completed s = mellin (fun t => (theta t - 1) / 2) (s / 2) := by
  rw [mellin_div_const, completed]
  congr 1
  exact (thetaPair.hasMellin (by change (1 / 2 : ℝ) < (s / 2).re; simpa using
    (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hs)).2.symm

theorem completed_eq_gamma_mul_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    completed s = Gammaℝ s * series s := by
  have hsum : Summable (fun n : ℕ => ‖(1 : ℂ)‖ / |(n : ℝ) + 1| ^ s.re) := by
    have h := Real.summable_one_div_nat_rpow.mpr hs
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑(_ : ℕ) + 1))] using
      (summable_nat_add_iff 1).mpr h
  have hF (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun n : ℕ => if (n : ℝ) + 1 = 0 then 0 else
        (1 : ℂ) * (Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) : ℂ))
        ((theta t - 1) / 2) := by
    have hn (n : ℕ) : (n : ℝ) + 1 ≠ 0 := by positivity
    simpa only [hn, ite_false, one_mul] using hasSum_gaussian ht
  have h := hasSum_mellin_pi_mul_sq (a := fun _ : ℕ => (1 : ℂ))
    (r := fun n => (n : ℝ) + 1) (lt_trans zero_lt_one hs) hF hsum
  rw [completed_eq_mellin hs, ← h.tsum_eq]
  simp_rw [mul_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑(_ : ℕ) + 1)),
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    div_eq_mul_inv]
  rw [tsum_mul_left]
  simp only [series, one_div]

end Gaussian

/-- An ambient representative of the continuation, used away from `1`.
The shifted reciprocal Gamma factor cancels the apparent singularity at zero. -/
def mellinExtension (s : ℂ) : ℂ :=
  (Gaussian.entirePart s - 1 / (1 - s)) * (Gammaℝ s)⁻¹ -
    (Gammaℝ (s + 2))⁻¹ / (2 * (Real.pi : ℂ))

theorem differentiableAt_mellinExtension {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ mellinExtension s := by
  have hden : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs.symm
  exact (((Gaussian.differentiable_entirePart s).sub
    ((differentiableAt_const 1).div ((differentiableAt_const 1).sub differentiableAt_id) hden)).mul
      (differentiable_Gammaℝ_inv s)).sub
    (((differentiable_Gammaℝ_inv (s + 2)).comp s (differentiableAt_id.add_const 2)).div_const _)

theorem analyticOnNhd_mellinExtension : AnalyticOnNhd ℂ mellinExtension {1}ᶜ :=
  (show DifferentiableOn ℂ mellinExtension {1}ᶜ from
    fun _ hs => (differentiableAt_mellinExtension hs).differentiableWithinAt).analyticOnNhd
      isOpen_compl_singleton

theorem mellinExtension_eq_completed_div {s : ℂ} (hs : s ≠ 0) :
    mellinExtension s = Gaussian.completed s / Gammaℝ s := by
  rw [mellinExtension, Gaussian.completed_eq, Gammaℝ_add_two hs]
  by_cases hg : Gammaℝ s = 0
  · simp [hg]
  · have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring

/-- Agreement is proved from the original sum, not from an imported zeta function. -/
theorem mellinExtension_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    mellinExtension s = series s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [rightHalfPlane, h] at hs
  rw [mellinExtension_eq_completed_div hs0, Gaussian.completed_eq_gamma_mul_series hs]
  exact mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs))

theorem mellinExtension_germ_eq_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    mellinExtension =ᶠ[𝓝 s] series :=
  Filter.eventually_of_mem (isOpen_rightHalfPlane.mem_nhds hs)
    fun _ hz => mellinExtension_eq_series hz

/-- Entire extension of `(s-1) ζ(s)`, with the pole removed algebraically. -/
def poleRemoved (s : ℂ) : ℂ :=
  (s - 1) * (Gaussian.entirePart s * (Gammaℝ s)⁻¹ -
    (Gammaℝ (s + 2))⁻¹ / (2 * (Real.pi : ℂ))) + (Gammaℝ s)⁻¹

theorem differentiable_poleRemoved : Differentiable ℂ poleRemoved := by
  exact ((differentiable_id.sub_const 1).mul
    ((Gaussian.differentiable_entirePart.mul differentiable_Gammaℝ_inv).sub
      ((differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2)).div_const _))).add
        differentiable_Gammaℝ_inv

theorem sub_one_mul_mellinExtension {s : ℂ} (hs : s ≠ 1) :
    (s - 1) * mellinExtension s = poleRemoved s := by
  unfold mellinExtension poleRemoved
  have h : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs.symm
  field_simp
  ring

@[simp] theorem poleRemoved_one : poleRemoved 1 = 1 := by simp [poleRemoved]

/-- The unique possible singularity is a genuine simple pole, of residue one. -/
theorem mellinExtension_residue_one :
    Tendsto (fun s => (s - 1) * mellinExtension s) (𝓝[≠] 1) (𝓝 1) := by
  have h : Tendsto poleRemoved (𝓝[≠] (1 : ℂ)) (𝓝 (poleRemoved 1)) :=
    (differentiable_poleRemoved.continuous.tendsto 1).mono_left nhdsWithin_le_nhds
  rw [poleRemoved_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (sub_one_mul_mellinExtension hs).symm

@[simp] theorem mellinExtension_zero : mellinExtension 0 = -1 / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  norm_num [mellinExtension, Gammaℝ_def, Complex.cpow_neg_one]
  field_simp

/-- The continuation has the expected trivial zeros in the left half-plane. -/
theorem mellinExtension_neg_even (n : ℕ) : mellinExtension (-2 * (n + 1)) = 0 := by
  have hs : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (by norm_cast)
  rw [mellinExtension_eq_completed_div hs,
    Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by push_cast; ring⟩, div_zero]

end RiemannZeta
