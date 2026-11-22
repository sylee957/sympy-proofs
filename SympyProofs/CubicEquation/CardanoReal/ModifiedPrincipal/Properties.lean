module

public import SympyProofs.RealCubeRoot.ModifiedPrincipal.Properties
public import SympyProofs.CubicEquation.CardanoReal.Basic
public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Formula

/-!
# Properties of the modified-principal Cardano pair

For real depressed coefficients `p,q`, the two modified principal cube roots of
the Cardano radicands form a compatible pair directly: their product is
`-p / 3`, with no division by a radical, nonzero-radicand hypothesis, or
conditional. Their sum is real, and the three paired expressions are exactly
the roots of the depressed cubic, including repeated and triple roots.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
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

/-- The first of the three Cardano solutions is always real. -/
theorem modifiedPrincipal_cardano_first_im (a b c d : ℝ) :
    (modifiedPrincipalCubicRoots a b c d).x₀.im = 0 := by
  have h := modifiedPrincipal_pair_sum_im (c / a - (b / a) ^ 2 / 3)
    (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a)
  simpa only [modifiedPrincipalCubicRoots, radicandPlus, radicandMinus, discriminant_ofReal,
    realDiscriminant, Complex.sub_im, Complex.ofReal_im, sub_zero] using h

end CubicEquation.CardanoReal
