module

public import SympyProofs.Binomial.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pochhammer

/-!
# Entire polynomial slices of SymPy's integer-lower binomial

For every fixed integer `k`, `choose z k` is entire in the complex variable `z`:
a polynomial for `k ≥ 0`, and the zero function for `k < 0`. These values include
all negative upper integers. The jointly entire circle-integral extension lives in
`UniqueExteensions/CircleIntegral.lean`.
-/

@[expose] public section

noncomputable section
namespace SympyBinomial

/-- Every integer-lower slice is differentiable at every complex upper argument. -/
theorem differentiable_choose (k : ℤ) : Differentiable ℂ (fun z : ℂ => choose z k) := by
  by_cases hk : k < 0
  · simpa only [choose_of_neg _ hk] using (differentiable_const (0 : ℂ))
  · have heq : (fun z : ℂ => choose z k) =
        fun z => (descPochhammer ℂ k.toNat).eval z / (k.toNat.factorial : ℂ) := by
      funext z
      rw [← Int.toNat_of_nonneg (le_of_not_gt hk)]
      exact choose_eq_descPochhammer z k.toNat
    rw [heq]
    exact differentiable_descPochhammer_eval.div_const _

/-- Every integer-lower slice has a convergent complex power series at every point. -/
theorem analyticAt_choose (k : ℤ) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => choose t k) z :=
  (differentiable_choose k).analyticAt z

/-- The polynomial or zero slice is entire, including at negative upper integers. -/
theorem analyticOnNhd_choose (k : ℤ) :
    AnalyticOnNhd ℂ (fun z : ℂ => choose z k) Set.univ :=
  fun z _ => analyticAt_choose k z

end SympyBinomial
