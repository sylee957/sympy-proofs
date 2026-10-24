module

public import SympyProofs.RealCubeRoot.ModifiedPrincipal
public import SympyProofs.RealCubeRoot.Cardano.ConjugateCorrected
public import SympyProofs.RealCubeRoot.Cardano.PhaseCorrected

/-!
# Modified principal cube roots with conjugate correction

Start with `U = modifiedPrincipal A` and `W = modifiedPrincipal B`. Apply the
conjugation-based zero detector to pair them with `C = -p/3`. Since both are
cube roots and `A*B = C^3`, the corrected pair gives all three roots for arbitrary
complex coefficients. The denominator is always positive real, including at zero.

See `ModifiedConjugateCorrectedRealness.lean` for the reduction to the direct
modified-principal formula on real coefficients and realness of the first root.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- The first radical uses the conjugation-compatible modified principal root. -/
def modifiedConjugateCorrectedU (p q : ℂ) : ℂ :=
  modifiedPrincipal (radicandPlus p q)

/-- Pair the modified principal radicals using the conjugation-based zero detector. -/
def modifiedConjugateCorrectedV (p q : ℂ) : ℂ :=
  conjugatePairedRoot (modifiedConjugateCorrectedU p q)
    (modifiedPrincipal (radicandMinus p q)) (-p / 3)

@[simp] theorem modifiedConjugateCorrectedU_cube (p q : ℂ) :
    modifiedConjugateCorrectedU p q ^ 3 = radicandPlus p q :=
  modifiedPrincipal_cube _

/-- Both Cardano pairing identities hold, including when either radical is zero. -/
theorem modifiedConjugateCorrected_pair (p q : ℂ) :
    modifiedConjugateCorrectedV p q ^ 3 = radicandMinus p q ∧
      modifiedConjugateCorrectedU p q * modifiedConjugateCorrectedV p q = -p / 3 := by
  have h : modifiedConjugateCorrectedU p q ^ 3 *
      modifiedPrincipal (radicandMinus p q) ^ 3 = (-p / 3) ^ 3 := by
    rw [modifiedConjugateCorrectedU_cube, modifiedPrincipal_cube, radicands_product]
  simpa only [modifiedConjugateCorrectedV, modifiedPrincipal_cube] using
    conjugatePairedRoot_spec h

/-- The combined formula never divides by zero in the pairing correction. -/
theorem modifiedConjugateCorrected_denominator_ne_zero (p q : ℂ) :
    let u := modifiedConjugateCorrectedU p q
    let r := u * conj u
    r + conjugateZeroDetector r ≠ 0 :=
  conjugatePairedRoot_denominator_ne_zero _

/-- All three roots for arbitrary complex coefficients. The formula uses only
principal radicals, conjugation, and arithmetic; the correction denominator is
nonzero by `modifiedConjugateCorrected_denominator_ne_zero`. -/
theorem cardano_formula_modifiedConjugateCorrected {a : ℂ} (ha : a ≠ 0)
    (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
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
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  extract_lets p q Δ A B C η T E U W r e V ω shift x₀ x₁ x₂
  have hU : U = modifiedConjugateCorrectedU p q := rfl
  have hV : V = modifiedConjugateCorrectedV p q := rfl
  apply cubic_formula_of_compatible_pair ha b c d x U V
  · rw [hU, hV, modifiedConjugateCorrectedU_cube,
      (modifiedConjugateCorrected_pair p q).1, radicands_sum]
    rfl
  · rw [hU, hV]
    exact (modifiedConjugateCorrected_pair p q).2

end RealCubeRoot.Cardano
