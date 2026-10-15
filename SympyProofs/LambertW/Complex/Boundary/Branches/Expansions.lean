import SympyProofs.LambertW.Complex.Boundary.Branches.Compatibility
import SympyProofs.LambertW.Complex.Principal.Puiseux

/-! # Principal branch-point formulas through the unified indexed API -/
namespace LambertW.Complex
open Filter Topology

theorem tendsto_norm_branchWithBoundary_zero_div_sqrt (side : BoundarySide) :
    Tendsto (fun z : ℂ => ‖branchWithBoundary 0 side z + 1‖ /
        Real.sqrt ‖z - ((-Real.exp (-1) : ℝ) : ℂ)‖)
      (𝓝[≠] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (Real.sqrt (2 * Real.exp 1))) := by
  simpa only [branchWithBoundary_zero_eq_model] using
    BoundaryInternal.tendsto_norm_principalModel_div_sqrt side

theorem exists_branchWithBoundary_zero_puiseux :
    ∃ P R : ℂ → ℂ, AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R 0 ∧
      P 0 = 0 ∧ HasDerivAt P 1 0 ∧
      (∀ side : BoundarySide, ∀ z : ℂ,
        P (branchWithBoundary 0 side z + 1) ^ 2 =
          2 * Complex.exp 1 * (z - ((-Real.exp (-1) : ℝ) : ℂ))) ∧
      (∀ side : BoundarySide, ∀ᶠ z in 𝓝 (((-Real.exp (-1) : ℝ) : ℂ)),
        let p := P (branchWithBoundary 0 side z + 1)
        branchWithBoundary 0 side z = -1 + p - p ^ 2 / 3 +
          (11 / 72 : ℂ) * p ^ 3 + p ^ 4 * R p) := by
  simpa only [branchWithBoundary_zero_eq_model] using exists_principal_puiseux_expansion

end LambertW.Complex
