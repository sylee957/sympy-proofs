module

public import SympyProofs.Sum.RationalSum.Algorithm
public import SympyProofs.Sum.RationalSum.Basic
public import SympyProofs.Sum.RationalSum.Correctness

/-!
# Parametric rational summation with fixed denominator

Call `RationalSum.reduce ops P D` with `P : Polynomial R`, where `R` is any
commutative ℚ-algebra, a nonzero rational denominator `D`, and shiftless
decomposition primitives `ops`. The output consists of a polynomial primitive,
compact shift-sum certificate, and residual numerators.

The noncomputable definition uses Mathlib's `/ₘ` and `%ₘ` directly. All divisors
used on parameter-valued numerators are monic rational polynomials mapped into
`R`. Classical equality is internal to the mathematical definitions; no
`DecidableEq R` instance is required from callers.

`reduce_eq_model` connects the imperative definition to its fold model.
`reduce_sound` proves `P/D = ΔG + residual` for the returned polynomials.

`reduce_map` proves compatibility with every ℚ-algebra homomorphism, including
specializations that lower the numerator degree. `reduce_apply` covers arbitrary
function-valued coefficients. Soundness, summability, and finite-sum theorems
hold after every specialization.

`reduce_summable_iff` characterizes rational summability by vanishing residual
numerators. This is a proposition, not a decision procedure for arbitrary
parameter functions.
-/
