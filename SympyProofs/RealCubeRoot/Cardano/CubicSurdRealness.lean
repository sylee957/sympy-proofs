module

public import SympyProofs.RealCubeRoot.Cardano.CubicSurd

/-!
# Realness of the first cubic-surd Cardano root

For either surd extension, the first Cardano expression is real for all real
coefficients, regardless of the sign of the discriminant.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- The first Cardano expression has zero imaginary part for either surd extension
and every real discriminant. For `a ≠ 0`, `cardano_formula_cubicSurd` also proves
that this expression solves the cubic. Realness alone needs no assumption on `a`. -/
theorem cubicSurd_cardano_first_im (S : ℂ → ℂ)
    (hS : S = cubicSurdLeft ∨ S = cubicSurdRight) (a b c d : ℝ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let s := Complex.sqrt (Δ : ℂ)
    let u := S (-(q : ℂ) / 2 + s)
    let v := S (-(q : ℂ) / 2 - s)
    let shift : ℝ := (b / a) / 3
    let x₀ := u + v - (shift : ℂ)
    x₀.im = 0 := by
  have hconj : ∀ z, S (conj z) = conj (S z) := by
    rcases hS with rfl | rfl
    · exact cubicSurdLeft_conj
    · exact cubicSurdRight_conj
  have hsum (p q : ℝ) :
      (S (radicandPlus (p : ℂ) q) + S (radicandMinus (p : ℂ) q)).im = 0 :=
    Complex.conj_eq_iff_im.mp (direct_pair_conj_of_conj S hconj p q).1
  dsimp only
  simpa only [radicandPlus, radicandMinus, discriminant_ofReal, realDiscriminant,
    Complex.sub_im, Complex.ofReal_im, sub_zero] using
    hsum (c / a - (b / a) ^ 2 / 3)
      (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a)

end RealCubeRoot.Cardano
