import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Tactic

/-!
# Gaussian kernel for continuation of the defining series

This file uses the Gaussian theta sum and its transformation law, not any
Riemann or Hurwitz zeta definitions. Rapid decay and the transformation law
allow the general Mellin-transform continuation theorem to be applied.
-/

noncomputable section
namespace RiemannZeta
namespace Gaussian

open Complex Filter Asymptotics Set MeasureTheory
open scoped Topology

/-- The Gaussian sum `∑ n : ℤ, exp (-π n² t)`. -/
def theta (t : ℝ) : ℂ := jacobiTheta (I * t)

theorem continuousOn_theta : ContinuousOn theta (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  exact (continuousAt_jacobiTheta (by simpa using ht)).comp (by fun_prop)

theorem theta_inversion {t : ℝ} (ht : 0 < t) :
    theta (1 / t) = (t ^ (1 / 2 : ℝ) : ℝ) * theta t := by
  let τ : UpperHalfPlane := ⟨I * t, by simpa using ht⟩
  have h := jacobiTheta_S_smul τ
  have hinv : (-(I * (t : ℂ)))⁻¹ = I * (1 / t : ℝ) := by
    push_cast
    simp [inv_I, mul_comm]
  have hbase : -I * (I * (t : ℂ)) = (t : ℂ) := by simp [← mul_assoc]
  have hpow : (t : ℂ) ^ (1 / 2 : ℂ) = (t ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow ht.le (1 / 2 : ℝ)).symm
  simpa only [UpperHalfPlane.modular_S_smul, τ, UpperHalfPlane.coe_mk,
    hinv, hbase, hpow, theta] using h

theorem theta_sub_one_isBigO (r : ℝ) :
    (fun t => theta t - 1) =O[atTop] (fun t : ℝ => t ^ r) := by
  have ht : Tendsto (fun t : ℝ => I * (t : ℂ)) atTop (comap Complex.im atTop) := by
    rw [tendsto_comap_iff]
    have hf : Complex.im ∘ (fun t : ℝ => I * (t : ℂ)) = id := by
      ext t
      simp
    rw [hf]
    exact tendsto_id
  have h := isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto ht
  have h' : (fun t => theta t - 1) =O[atTop] (fun t : ℝ => Real.exp (-Real.pi * t)) := by
    simpa [theta, Function.comp_def] using h
  exact h'.trans (isLittleO_exp_neg_mul_rpow_atTop Real.pi_pos r).isBigO

/-- The weight-one-half functional-equation data derived from the Gaussian sum. -/
def thetaPair : WeakFEPair ℂ where
  f := theta
  g := theta
  k := 1 / 2
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := continuousOn_theta.locallyIntegrableOn measurableSet_Ioi
  hg_int := continuousOn_theta.locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq t ht := by simpa [smul_eq_mul] using theta_inversion ht
  hf_top := theta_sub_one_isBigO
  hg_top := theta_sub_one_isBigO

theorem thetaPair_symm : thetaPair.symm = thetaPair := by
  unfold WeakFEPair.symm thetaPair
  congr 1
  simp

/-- Positive-integer Gaussian terms sum to half of the theta sum with its
constant term removed. This is the link to the original Dirichlet series. -/
theorem hasSum_gaussian {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) : ℂ))
      ((theta t - 1) / 2) := by
  have h := hasSum_nat_jacobiTheta (τ := I * t) (by simpa using ht)
  refine h.congr_fun fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp only [I_sq]
  ring

end Gaussian
end RiemannZeta
