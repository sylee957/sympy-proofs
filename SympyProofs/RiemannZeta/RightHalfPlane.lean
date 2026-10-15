import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Tactic

/-!
# The defining zeta series on the right half-plane

The starting point is the absolutely convergent series `∑ n ≥ 1, n⁻ˢ`.
`zeta` has domain `{s : ℂ // 1 < s.re}`. No analytic continuation or values
outside this domain are defined here.

`series` is the ambient `tsum` expression used to state complex differentiability.
Lean totalizes `tsum`; its values outside the convergence domain are not an
analytic continuation. General Dirichlet-series results establish holomorphy;
no Riemann or Hurwitz zeta definitions or results are used.
-/

noncomputable section
namespace RiemannZeta

open Filter
open scoped Topology

/-- The open domain of the defining series. -/
def rightHalfPlane : Set ℂ := {s | 1 < s.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Ambient series expression, used only on `rightHalfPlane`. -/
def series (s : ℂ) : ℂ := ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s

/-- The zeta function at this stage is defined only for `1 < re s`. -/
def zeta (s : rightHalfPlane) : ℂ := series s

theorem summable_iff (s : ℂ) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) ↔ s ∈ rightHalfPlane := by
  simpa only [rightHalfPlane, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℂ) ^ s)).trans
      Complex.summable_one_div_nat_cpow

theorem hasSum_zeta (s : rightHalfPlane) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (s : ℂ)) (zeta s) :=
  ((summable_iff s).mpr s.property).hasSum

theorem summable_norm (s : rightHalfPlane) :
    Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ (s : ℂ)‖) :=
  ((summable_iff s).mpr s.property).norm

theorem tendsto_partialSums (s : rightHalfPlane) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ (s : ℂ))
      atTop (𝓝 (zeta s)) :=
  (hasSum_zeta s).tendsto_sum_nat

private theorem abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, by simp⟩

private theorem series_eq_LSeries {s : ℂ} (hs : s ∈ rightHalfPlane) :
    series s = LSeries (fun _ : ℕ => 1) s := by
  have h : LSeriesSummable (fun _ : ℕ => 1) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by simp) hs
  change series s = ∑' n, LSeries.term (fun _ : ℕ => 1) s n
  rw [h.tsum_eq_zero_add]
  simp [series, LSeries.term]

/-- Holomorphy of the defining series on its original domain. -/
theorem differentiableOn_series : DifferentiableOn ℂ series rightHalfPlane := by
  have h : DifferentiableOn ℂ (LSeries (fun _ : ℕ => 1)) rightHalfPlane :=
    (LSeries_differentiableOn _).mono fun s hs =>
      abscissa_le_one.trans_lt (by exact_mod_cast hs)
  exact h.congr fun s hs => series_eq_LSeries hs

theorem analyticOnNhd_series : AnalyticOnNhd ℂ series rightHalfPlane :=
  differentiableOn_series.analyticOnNhd isOpen_rightHalfPlane

theorem differentiableAt_series {s : ℂ} (hs : s ∈ rightHalfPlane) :
    DifferentiableAt ℂ series s :=
  differentiableOn_series.differentiableAt (isOpen_rightHalfPlane.mem_nhds hs)

end RiemannZeta
