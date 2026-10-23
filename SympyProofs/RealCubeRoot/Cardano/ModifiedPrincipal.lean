module

public import SympyProofs.RealCubeRoot.ModifiedPrincipal
public import SympyProofs.RealCubeRoot.Cardano.CubicSurd

/-!
# Cardano's formula with modified principal cube roots

For real coefficients, `modifiedPrincipal` supplies a compatible pair of cube
roots directly. No division by a radical, nonzero-radicand hypothesis, or
conditional is needed. The formula includes repeated and triple roots.

`cardano_formula_modifiedPrincipal` displays the complete expression,
including the principal-root and conjugation construction, using `let` bindings.
Its coefficients are real; its three solutions are allowed to be complex.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- The direct radicals have the product required by Cardano, even if one is zero. -/
theorem modifiedPrincipal_pair_product (p q : ℝ) :
    modifiedPrincipal (radicandPlus (p : ℂ) q) *
      modifiedPrincipal (radicandMinus (p : ℂ) q) = -(p : ℂ) / 3 :=
  direct_pair_product_of_cube_conj modifiedPrincipal
    modifiedPrincipal_cube modifiedPrincipal_conj p q

/-- The first depressed Cardano expression is always real. -/
theorem modifiedPrincipal_pair_sum_im (p q : ℝ) :
    (modifiedPrincipal (radicandPlus (p : ℂ) q) +
      modifiedPrincipal (radicandMinus (p : ℂ) q)).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (direct_pair_conj_of_conj modifiedPrincipal modifiedPrincipal_conj p q).1

/-- All three expressions, with multiplicities, solve precisely the depressed cubic. -/
theorem mem_modifiedPrincipal_pairedRoots_iff (p q : ℝ) (x : ℂ) :
    x ∈ pairedRoots (modifiedPrincipal (radicandPlus (p : ℂ) q))
      (modifiedPrincipal (radicandMinus (p : ℂ) q)) ↔
      x ^ 3 + (p : ℂ) * x + q = 0 := by
  apply mem_pairedRoots_iff
  · rw [modifiedPrincipal_cube, modifiedPrincipal_cube, radicands_sum]
  · exact modifiedPrincipal_pair_product p q

/-- A uniform formula for all real cubics with nonzero leading coefficient.
The cube-root construction and both radicals are explicit; the only variable
denominator is the nonzero leading coefficient `a`. -/
theorem cardano_formula_modifiedPrincipal {a : ℝ} (ha : a ≠ 0)
    (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let η : ℂ := (1 + (Real.sqrt 3 : ℂ) * I) / 2
    let T : ℂ → ℂ := fun z => η * principal z + conj η * conj (principal (conj z))
    let s := Complex.sqrt (Δ : ℂ)
    let u := T (-(q : ℂ) / 2 + s)
    let v := T (-(q : ℂ) / 2 - s)
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift : ℝ := (b / a) / 3
    let x₀ := u + v - (shift : ℂ)
    let x₁ := ω * u + ω ^ 2 * v - (shift : ℂ)
    let x₂ := ω ^ 2 * u + ω * v - (shift : ℂ)
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  simpa only [modifiedPrincipal, pairedRoots, radicandPlus, radicandMinus,
    discriminant_ofReal, realDiscriminant, omega, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, Complex.ofReal_div,
    Complex.ofReal_ofNat] using
    (symmetric_cubic_roots_iff_of_cube_conj modifiedPrincipal
      modifiedPrincipal_cube modifiedPrincipal_conj ha b c d x).symm

/-- The shift back to the original cubic preserves realness of the first expression. -/
theorem modifiedPrincipal_cardano_first_im (a b c d : ℝ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    (modifiedPrincipal (radicandPlus (p : ℂ) q) +
      modifiedPrincipal (radicandMinus (p : ℂ) q) - ((b / a) / 3 : ℝ)).im = 0 := by
  dsimp only
  rw [Complex.sub_im, modifiedPrincipal_pair_sum_im, Complex.ofReal_im, sub_zero]

end RealCubeRoot.Cardano
