module

public import SympyProofs.Binomial.UniqueExteensions.Interpolation

/-!
# The centered circle-integral extension

For `0 < r < 1`, define

  C_r(z,w) = (1/(2π)) ∫_{-π}^{π} exp(z log(1+r exp(it)) - w(log r + it)) dt.

This file proves joint entire analyticity, exact agreement with every integer-lower
slice of SymPy's binomial, and Pascal's identity for all complex arguments.
The centered interval is a normalization choice; `circleIntegralChoose` instead
uses `[0,2π]`. Both constructions agree at integer lower arguments.

`SamplingUniqueness.lean` characterizes this centered construction by polynomial
integer-lower slices and a weighted square-integrable Fourier representation.
-/

@[expose] public section

noncomputable section

namespace SympyBinomial

/-- The circle interpolation centered at angle zero, integrated from `-π` to `π`. -/
def centeredCircleChoose (r : InterpolationRadius) (z w : ℂ) : ℂ :=
  angleCircleChoose r (-Real.pi) z w

theorem analyticOnNhd_centeredCircleChoose (r : InterpolationRadius) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => centeredCircleChoose r p.1 p.2) Set.univ :=
  fun p _ => analyticAt_angleCircleChoose r (-Real.pi) p

theorem centeredCircleChoose_int_eq_choose (r : InterpolationRadius) (z : ℂ) (k : ℤ) :
    centeredCircleChoose r z (k : ℂ) = choose z k :=
  angleCircleChoose_int_eq_choose r (-Real.pi) z k

theorem centeredCircleChoose_intCast_intCast (r : InterpolationRadius) (n k : ℤ) :
    centeredCircleChoose r (n : ℂ) (k : ℂ) = ((choose n k : ℤ) : ℂ) := by
  rw [centeredCircleChoose_int_eq_choose, intCast_choose]

theorem centeredCircleChoose_pascal (r : InterpolationRadius) (z w : ℂ) :
    centeredCircleChoose r z w =
      centeredCircleChoose r (z - 1) w + centeredCircleChoose r (z - 1) (w - 1) :=
  angleCircleChoose_pascal r (-Real.pi) z w

/-- The centered family is an entire extension of the same FCK convention. -/
theorem isEntireBinomial_centeredCircleChoose (r : InterpolationRadius) :
    IsEntireBinomial (centeredCircleChoose r) :=
  ⟨analyticOnNhd_centeredCircleChoose r, centeredCircleChoose_intCast_intCast r,
    centeredCircleChoose_pascal r⟩

end SympyBinomial
