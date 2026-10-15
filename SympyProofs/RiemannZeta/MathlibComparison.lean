import SympyProofs.RiemannZeta.ExtendedValues
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Comparison with mathlib's Riemann zeta function

This module is the bridge to mathlib's zeta definition. The preceding
construction does not depend on that definition. Equality away from the pole
follows from agreement with the original series and our continuation uniqueness
theorem. At the pole, our complex-valued function assigns zero; comparison of
total functions therefore uses an explicit update. The sphere-valued versions
agree everywhere when both assign infinity at the pole.
-/

noncomputable section
namespace RiemannZeta
open Set
open scoped OnePoint

/-- Our path-continued zeta agrees with mathlib's zeta away from the pole. -/
theorem continuedZeta_eq_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    continuedZeta s = riemannZeta s := by
  apply Eq.symm
  apply extension_unique analyticOn_riemannZeta _ hs
  intro z hz
  exact zeta_eq_tsum_one_div_nat_add_one_cpow hz

/-- Exact equality of total complex-valued functions after matching the
arbitrary convention at the pole. -/
theorem continuedZeta_eq_update_riemannZeta :
    continuedZeta = Function.update riemannZeta 1 0 := by
  funext s
  by_cases hs : s = 1
  · subst s
    simp
  · rw [Function.update_of_ne hs, continuedZeta_eq_riemannZeta hs]

/-- Away from the pole, the extended value is the embedding of mathlib's zeta. -/
theorem extendedZeta_eq_coe_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    extendedZeta s = (riemannZeta s : OnePoint ℂ) := by
  rw [extendedZeta_of_ne_one hs, continuedZeta_eq_riemannZeta hs]

/-- The two sphere-valued versions coincide on all inputs, including the pole. -/
theorem extendedZeta_eq_riemannZeta_with_infty :
    extendedZeta = fun s : ℂ =>
      if s = 1 then (∞ : OnePoint ℂ) else (riemannZeta s : OnePoint ℂ) := by
  funext s
  by_cases hs : s = 1
  · subst s
    simp
  · simp [hs, extendedZeta_eq_coe_riemannZeta hs]

end RiemannZeta
