module

public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Properties

/-!
# Cardano's formula with an explicit piecewise principal root

For real coefficients, `piecewisePrincipal` changes the principal cube root
only on the negative real axis. It equals `modifiedPrincipal`, so the symmetric
formula has an always-real first root.

The complete formula appears in `cardano_formula_piecewise_real`, with each
conditional visible.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex
open scoped ComplexConjugate

/-- Use the real cube root on the negative real axis and the principal cube
root everywhere else, including zero. -/
def piecewisePrincipal (z : ℂ) : ℂ :=
  if z.im = 0 ∧ z.re < 0 then -principal (-z) else principal z

/-- The piecewise rule is exactly the existing conjugation expression. -/
theorem piecewisePrincipal_eq_modifiedPrincipal (z : ℂ) :
    piecewisePrincipal z = modifiedPrincipal z := by
  by_cases him : z.im = 0
  · have hreal : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [him]
    rw [← hreal, modifiedPrincipal_ofReal]
    by_cases hre : z.re < 0
    · simp only [piecewisePrincipal, ofReal_im, ofReal_re, hre, and_self,
        ↓reduceIte, ← ofReal_neg,
        principal_ofReal_of_nonneg (by linarith : 0 ≤ -z.re)]
      simp [realCubicSurd, hre]
    · simp [piecewisePrincipal, hre, principal_ofReal_of_nonneg (le_of_not_gt hre),
        realCubicSurd]
  · simpa [piecewisePrincipal, him] using
      (modifiedPrincipal_eq_principal (Or.inr him)).symm

@[simp] theorem piecewisePrincipal_cube (z : ℂ) : piecewisePrincipal z ^ 3 = z := by
  rw [piecewisePrincipal_eq_modifiedPrincipal, modifiedPrincipal_cube]

@[simp] theorem piecewisePrincipal_conj (z : ℂ) :
    piecewisePrincipal (conj z) = conj (piecewisePrincipal z) := by
  simp only [piecewisePrincipal_eq_modifiedPrincipal, modifiedPrincipal_conj]

/-- Real coefficients: both radicals use the same explicit piecewise rule.
The solutions themselves are allowed to be complex. -/
theorem cardano_formula_piecewise_real {a : ℝ} (ha : a ≠ 0)
    (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ)
    let B := -(q : ℂ) / 2 - Complex.sqrt (Δ : ℂ)
    let u := if A.im = 0 ∧ A.re < 0 then -principal (-A) else principal A
    let v := if B.im = 0 ∧ B.re < 0 then -principal (-B) else principal B
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift : ℝ := (b / a) / 3
    let x₀ := u + v - (shift : ℂ)
    let x₁ := ω * u + ω ^ 2 * v - (shift : ℂ)
    let x₂ := ω ^ 2 * u + ω * v - (shift : ℂ)
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  simpa only [piecewisePrincipal, pairedRoots, radicandPlus, radicandMinus,
    discriminant_ofReal, realDiscriminant, omega, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, Complex.ofReal_div,
    Complex.ofReal_ofNat] using
    (symmetric_cubic_roots_iff_of_cube_conj piecewisePrincipal
      piecewisePrincipal_cube piecewisePrincipal_conj ha b c d x).symm

/-- The first expression in the real-coefficient formula is always real,
without a hypothesis on the discriminant. -/
theorem piecewisePrincipal_cardano_first_im (a b c d : ℝ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    (piecewisePrincipal (radicandPlus (p : ℂ) q) +
      piecewisePrincipal (radicandMinus (p : ℂ) q) - ((b / a) / 3 : ℝ)).im = 0 := by
  simp only [piecewisePrincipal_eq_modifiedPrincipal]
  rw [Complex.sub_im, modifiedPrincipal_pair_sum_im, Complex.ofReal_im, sub_zero]

end CubicEquation.CardanoReal
