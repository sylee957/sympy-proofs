module

public import SympyProofs.LinearAlgebra.NeumannSeries.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Topology.Instances.Matrix

/-! Convergence of matrix power series in terms of the complex spectrum. -/

@[expose] public section

namespace SympyProofs.NeumannSeries

open Filter Matrix
open scoped Topology Matrix ENNReal NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The powers of a complex matrix tend to zero exactly when every eigenvalue lies in the open
unit disc. -/
theorem tendsto_complex_pow_zero_iff_spectrum (A : Matrix n n ℂ) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔ ∀ μ ∈ spectrum ℂ A, ‖μ‖ < 1 := by
  open scoped Matrix.Norms.Operator in
  constructor
  · intro h μ hμ
    have hlim : Tendsto (fun k : ℕ => ‖A ^ k‖ * ‖(1 : Matrix n n ℂ)‖) atTop (𝓝 0) := by
      simpa using h.norm.mul_const ‖(1 : Matrix n n ℂ)‖
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
    have hle := spectrum.norm_le_norm_mul_of_mem (spectrum.pow_mem_pow A k hμ)
    rw [norm_pow] at hle
    exact lt_of_pow_lt_pow_left₀ k zero_le_one (by simpa using hle.trans_lt hk)
  · intro h
    have hρ : spectralRadius ℂ A < 1 := by
      rcases (spectrum ℂ A).eq_empty_or_nonempty with he | hne
      · simp [spectralRadius_eq_of_unital, he]
      · exact_mod_cast spectrum.spectralRadius_lt_of_forall_lt_of_nonempty hne (r := 1)
          (fun μ hμ => by exact_mod_cast h μ hμ)
    obtain ⟨r, hr, hr1⟩ := exists_between hρ
    have hrtop : r ≠ ∞ := (hr1.trans ENNReal.one_lt_top).ne
    have hr' : r.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hrtop ENNReal.one_ne_top).mpr hr1
    have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually
      (gt_mem_nhds hr)
    refine squeeze_zero_norm' ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr')
    filter_upwards [hev, eventually_ne_atTop 0] with k hk hk0
    have hroot : ‖A ^ k‖ ^ (1 / k : ℝ) < r.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hrtop).mp hk
    calc ‖A ^ k‖ = (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k := by
          rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hk0]
      _ ≤ r.toReal ^ k := by gcongr

theorem summable_complex_pow_iff_spectrum (A : Matrix n n ℂ) :
    Summable (fun k : ℕ => A ^ k) ↔ ∀ μ ∈ spectrum ℂ A, ‖μ‖ < 1 :=
  (summable_pow_iff_tendsto_zero A).trans (tendsto_complex_pow_zero_iff_spectrum A)

/-- The polynomially weighted series `∑ k ^ p * A ^ k` converges exactly when every eigenvalue
lies in the open unit disc. -/
theorem summable_complex_pow_mul_pow_iff_spectrum (p : ℕ) (A : Matrix n n ℂ) :
    Summable (fun k : ℕ => (k : Matrix n n ℂ) ^ p * A ^ k) ↔ ∀ μ ∈ spectrum ℂ A, ‖μ‖ < 1 :=
  (summable_pow_mul_pow_iff_tendsto_zero p A).trans (tendsto_complex_pow_zero_iff_spectrum A)

lemma tendsto_map_ofReal_pow_zero_iff (A : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => A.map Complex.ofReal ^ k) atTop (𝓝 0) ↔
      Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  have hpow (k : ℕ) : A.map Complex.ofReal ^ k = (A ^ k).map Complex.ofReal :=
    (map_pow Complex.ofRealHom.mapMatrix A k).symm
  simp only [hpow]
  constructor
  · intro h
    have := ((continuous_id.matrix_map Complex.continuous_re).tendsto 0).comp h
    simpa [Function.comp_def, Matrix.map_map] using this
  · intro h
    have := ((continuous_id.matrix_map Complex.continuous_ofReal).tendsto 0).comp h
    simpa [Function.comp_def] using this

/-- The powers of a real matrix tend to zero exactly when every complex eigenvalue lies in the
open unit disc. -/
theorem tendsto_pow_zero_iff_spectrum (A : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔
      ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), ‖μ‖ < 1 :=
  (tendsto_map_ofReal_pow_zero_iff A).symm.trans (tendsto_complex_pow_zero_iff_spectrum _)

theorem summable_pow_iff_spectrum (A : Matrix n n ℝ) :
    Summable (fun k : ℕ => A ^ k) ↔ ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), ‖μ‖ < 1 :=
  (summable_pow_iff_tendsto_zero A).trans (tendsto_pow_zero_iff_spectrum A)

/-- The real polynomially weighted series `∑ k ^ p * A ^ k` converges exactly when every complex
eigenvalue lies in the open unit disc. -/
theorem summable_pow_mul_pow_iff_spectrum (p : ℕ) (A : Matrix n n ℝ) :
    Summable (fun k : ℕ => (k : Matrix n n ℝ) ^ p * A ^ k) ↔
      ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), ‖μ‖ < 1 :=
  (summable_pow_mul_pow_iff_tendsto_zero p A).trans (tendsto_pow_zero_iff_spectrum A)

end SympyProofs.NeumannSeries
