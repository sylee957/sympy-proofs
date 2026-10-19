module

public import SympyProofs.Binomial.UniqueExteensions.CircleIntegral
public import SympyProofs.Binomial.UniqueExteensions.Agreement

/-!
# Entire binomial properties of the circle integral

`IsEntireBinomial F` requires joint complex analyticity everywhere, agreement
with `choose n k` when both arguments are integers, and Pascal's identity for
all complex arguments. Agreement on entire integer-lower slices is not required.

`circleIntegralChoose` satisfies this specification. The centered variant and
the Fourier uniqueness theorems use the same predicate.
-/

@[expose] public section

noncomputable section

namespace SympyBinomial

/-- A jointly entire function matching SymPy at integer pairs and satisfying
Pascal's identity throughout the complex plane in both arguments. -/
structure IsEntireBinomial (F : ℂ → ℂ → ℂ) : Prop where
  analyticOnNhd : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) Set.univ
  intCast_intCast : AgreesWithSympyIntegers F
  pascal (z w : ℂ) : F z w = F (z - 1) w + F (z - 1) (w - 1)

/-- The integral construction satisfies the integer-pair specification. -/
theorem isEntireBinomial_circleIntegralChoose (r : InterpolationRadius) :
    IsEntireBinomial (circleIntegralChoose r) :=
  ⟨analyticOnNhd_circleIntegralChoose r, circleIntegralChoose_intCast_intCast r, circleIntegralChoose_pascal r⟩

end SympyBinomial
