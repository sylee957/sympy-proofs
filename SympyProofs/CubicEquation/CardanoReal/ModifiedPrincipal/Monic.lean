module

public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Formula

/-!
# Cardano's formula with modified principal cube roots for a monic cubic

`modifiedPrincipalMonicCubicRoots a b c` computes the three solutions of the
real monic cubic `x^3 + a*x^2 + b*x + c = 0`. It has no denominator that
depends on the coefficients.

`cardano_formula_modifiedPrincipal_monic` states that its three fields are
exactly the solutions. The general formula is the monic one applied to the
normalized coefficients, by `modifiedPrincipalCubicRoots_eq_monic`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- The three Cardano solutions of the real monic cubic
`x^3 + a*x^2 + b*x + c = 0`. Both cube roots are modified principal cube roots.
The first solution is real; the other two are allowed to be nonreal. -/
def modifiedPrincipalMonicCubicRoots (a b c : ℝ) : CardanoRoots :=
  let p : ℝ := b - a ^ 2 / 3
  let q : ℝ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
  let s := Complex.sqrt (Δ : ℂ)
  let u := modifiedPrincipal (-(q : ℂ) / 2 + s)
  let v := modifiedPrincipal (-(q : ℂ) / 2 - s)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift : ℝ := a / 3
  { x₀ := u + v - (shift : ℂ)
    x₁ := ω * u + ω ^ 2 * v - (shift : ℂ)
    x₂ := ω ^ 2 * u + ω * v - (shift : ℂ) }

/-- The general formula is the monic formula applied to the coefficients
divided by the leading one. -/
theorem modifiedPrincipalCubicRoots_eq_monic (a b c d : ℝ) :
    modifiedPrincipalCubicRoots a b c d =
      modifiedPrincipalMonicCubicRoots (b / a) (c / a) (d / a) :=
  rfl

/-- With leading coefficient `1` the general formula is the monic formula. -/
theorem modifiedPrincipalCubicRoots_one (a b c : ℝ) :
    modifiedPrincipalCubicRoots 1 a b c = modifiedPrincipalMonicCubicRoots a b c := by
  rw [modifiedPrincipalCubicRoots_eq_monic, div_one, div_one, div_one]

/-- The three fields of `modifiedPrincipalMonicCubicRoots a b c` are exactly the
solutions of `x^3 + a*x^2 + b*x + c = 0`, including repeated and triple roots. -/
theorem cardano_formula_modifiedPrincipal_monic (a b c : ℝ) (x : ℂ) :
    x ^ 3 + (a : ℂ) * x ^ 2 + (b : ℂ) * x + c = 0 ↔
      x = (modifiedPrincipalMonicCubicRoots a b c).x₀ ∨
      x = (modifiedPrincipalMonicCubicRoots a b c).x₁ ∨
      x = (modifiedPrincipalMonicCubicRoots a b c).x₂ := by
  have h := cardano_formula_modifiedPrincipal one_ne_zero a b c x
  rwa [modifiedPrincipalCubicRoots_one, ofReal_one, one_mul] at h

end CubicEquation.CardanoReal
