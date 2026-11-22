module

public import SympyProofs.RealCubeRoot.ModifiedPrincipal.Properties
public import SympyProofs.CubicEquation.CardanoReal.Basic

/-!
# Cardano's formula with modified principal cube roots

`modifiedPrincipalCubicRoots a b c d` computes the three solutions of the real
cubic `a*x^3 + b*x^2 + c*x + d = 0` as a `CardanoRoots` structure, taking
both cube roots with `modifiedPrincipal`. No division by a radical,
nonzero-radicand hypothesis, or conditional is needed.

`cardano_formula_modifiedPrincipal` states that for `a ≠ 0` its three fields are
exactly the solutions, including repeated and triple roots.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- Three complex solutions of a cubic, in the order Cardano's formula lists them. -/
@[ext] structure CardanoRoots where
  x₀ : ℂ
  x₁ : ℂ
  x₂ : ℂ

/-- The three Cardano solutions of the real cubic `a*x^3 + b*x^2 + c*x + d = 0`.
Both cube roots are modified principal cube roots, and the only variable
denominator is the leading coefficient `a`. The first solution is real; the
other two are allowed to be nonreal. -/
def modifiedPrincipalCubicRoots (a b c d : ℝ) : CardanoRoots :=
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
  let s := Complex.sqrt (Δ : ℂ)
  let u := modifiedPrincipal (-(q : ℂ) / 2 + s)
  let v := modifiedPrincipal (-(q : ℂ) / 2 - s)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift : ℝ := (b / a) / 3
  { x₀ := u + v - (shift : ℂ)
    x₁ := ω * u + ω ^ 2 * v - (shift : ℂ)
    x₂ := ω ^ 2 * u + ω * v - (shift : ℂ) }

/-- For every real cubic with nonzero leading coefficient, the three fields are
exactly its complex solutions. -/
theorem cardano_formula_modifiedPrincipal {a : ℝ} (ha : a ≠ 0)
    (b c d : ℝ) (x : ℂ) :
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = (modifiedPrincipalCubicRoots a b c d).x₀ ∨
      x = (modifiedPrincipalCubicRoots a b c d).x₁ ∨
      x = (modifiedPrincipalCubicRoots a b c d).x₂ := by
  simpa only [modifiedPrincipalCubicRoots, pairedRoots, radicandPlus, radicandMinus,
    discriminant_ofReal, realDiscriminant, omega, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, Complex.ofReal_div,
    Complex.ofReal_ofNat] using
    (symmetric_cubic_roots_iff_of_cube_conj modifiedPrincipal
      modifiedPrincipal_cube modifiedPrincipal_conj ha b c d x).symm

end CubicEquation.CardanoReal
