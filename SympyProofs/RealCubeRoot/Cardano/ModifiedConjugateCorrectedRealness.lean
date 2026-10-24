module

public import SympyProofs.RealCubeRoot.Cardano.ModifiedConjugateCorrected
public import SympyProofs.RealCubeRoot.Cardano.ModifiedPrincipal

/-!
# Realness of the first modified conjugate-corrected Cardano root

For real coefficients, the two modified principal radicals already have product
`-p/3`. The correction therefore leaves the second radical unchanged, even when
the first is zero. The resulting first root is exactly the real first root of
the symmetric modified-principal formula.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- For real coefficients, the correction returns the unmodified second radical. -/
theorem modifiedConjugateCorrectedV_ofReal (p q : ℝ) :
    modifiedConjugateCorrectedV (p : ℂ) q =
      modifiedPrincipal (radicandMinus (p : ℂ) q) :=
  conjugatePairedRoot_eq_of_mul_eq (modifiedPrincipal_pair_product p q)

/-- The first depressed root is real for every real discriminant. -/
theorem modifiedConjugateCorrected_pair_sum_im (p q : ℝ) :
    (modifiedConjugateCorrectedU (p : ℂ) q +
      modifiedConjugateCorrectedV (p : ℂ) q).im = 0 := by
  rw [modifiedConjugateCorrectedV_ofReal, modifiedConjugateCorrectedU]
  exact modifiedPrincipal_pair_sum_im p q

/-- The full combined formula has a real first expression for real coefficients.
For `a ≠ 0`, `cardano_formula_modifiedConjugateCorrected` also proves it is a root. -/
theorem modifiedConjugateCorrected_cardano_first_im (a b c d : ℝ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ)
    let B := -(q : ℂ) / 2 - Complex.sqrt (Δ : ℂ)
    let C := -(p : ℂ) / 3
    let η : ℂ := (1 + (Real.sqrt 3 : ℂ) * I) / 2
    let T : ℂ → ℂ := fun z => η * principal z + conj η * conj (principal (conj z))
    let E : ℂ → ℂ := fun r =>
      (principal (-1 + r * I) - conj (principal (-1 - r * I))) /
        (I * (Real.sqrt 3 : ℂ))
    let u := T A
    let w := T B
    let r := u * conj u
    let e := E r
    let v := (C * conj u + e * w) / (r + e)
    let shift : ℝ := (b / a) / 3
    let x₀ := u + v - (shift : ℂ)
    x₀.im = 0 := by
  dsimp only
  simpa only [modifiedConjugateCorrectedV, modifiedConjugateCorrectedU,
    conjugatePairedRoot, conjugateZeroDetector, modifiedPrincipal,
    radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant,
    Complex.sub_im, Complex.ofReal_im, sub_zero] using
    modifiedConjugateCorrected_pair_sum_im (c / a - (b / a) ^ 2 / 3)
      (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a)

end RealCubeRoot.Cardano
