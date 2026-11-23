module

public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Formula

/-!
# The modulus-and-phase formula for a monic cubic

`modulusPhaseMonicCubicRoots a b c` computes the three solutions of the complex
monic cubic `x^3 + a*x^2 + b*x + c = 0`. It has no denominator that depends on
the coefficients.

`cardano_formula_modulusPhase_monic` states that its three fields are exactly
the solutions. The general formula is the monic one applied to the normalized
coefficients, by `modulusPhaseCubicRoots_eq_monic`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open Complex
open scoped ComplexConjugate

/-- The linear coefficient of the depressed form of the complex cubic
`x^3 + a*x^2 + b*x + c`. -/
def complexMonicDepressedP (a b : ℂ) : ℂ := b - a ^ 2 / 3

/-- The constant coefficient of the depressed form of the complex cubic
`x^3 + a*x^2 + b*x + c`. -/
def complexMonicDepressedQ (a b c : ℂ) : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c

/-- The three Cardano solutions of the complex monic cubic
`x^3 + a*x^2 + b*x + c = 0`. The first radical `u` is a modified principal cube
root. The second radical `v` is built from a real cube root of a modulus and a
complex sign. -/
def modulusPhaseMonicCubicRoots (a b c : ℂ) : CardanoRoots :=
  let p := b - a ^ 2 / 3
  let q := 2 * a ^ 3 / 27 - a * b / 3 + c
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  let A := -q / 2 + Complex.sqrt Δ
  let B := -q / 2 - Complex.sqrt Δ
  let u := modifiedPrincipal A
  let v := ((‖B‖ ^ (3⁻¹ : ℝ) : ℝ) : ℂ) * unitPhase (-p * conj u) +
    ((1 - ‖unitPhase A‖ : ℝ) : ℂ) * modifiedPrincipal (-q)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift := a / 3
  { x₀ := u + v - shift
    x₁ := ω * u + ω ^ 2 * v - shift
    x₂ := ω ^ 2 * u + ω * v - shift }

/-- The general formula is the monic formula applied to the coefficients
divided by the leading one. -/
theorem modulusPhaseCubicRoots_eq_monic (a b c d : ℂ) :
    modulusPhaseCubicRoots a b c d = modulusPhaseMonicCubicRoots (b / a) (c / a) (d / a) :=
  rfl

/-- With leading coefficient `1` the general formula is the monic formula. -/
theorem modulusPhaseCubicRoots_one (a b c : ℂ) :
    modulusPhaseCubicRoots 1 a b c = modulusPhaseMonicCubicRoots a b c := by
  rw [modulusPhaseCubicRoots_eq_monic, div_one, div_one, div_one]

theorem modulusPhaseMonicCubicRoots_x₀_eq (a b c : ℂ) :
    (modulusPhaseMonicCubicRoots a b c).x₀ =
      modifiedConjugateCorrectedU (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) +
        modulusPhaseV (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) - a / 3 :=
  rfl

theorem modulusPhaseMonicCubicRoots_x₁_eq (a b c : ℂ) :
    (modulusPhaseMonicCubicRoots a b c).x₁ =
      omega *
          modifiedConjugateCorrectedU (complexMonicDepressedP a b)
            (complexMonicDepressedQ a b c) +
        omega ^ 2 * modulusPhaseV (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) -
          a / 3 :=
  rfl

theorem modulusPhaseMonicCubicRoots_x₂_eq (a b c : ℂ) :
    (modulusPhaseMonicCubicRoots a b c).x₂ =
      omega ^ 2 *
          modifiedConjugateCorrectedU (complexMonicDepressedP a b)
            (complexMonicDepressedQ a b c) +
        omega * modulusPhaseV (complexMonicDepressedP a b) (complexMonicDepressedQ a b c) -
          a / 3 :=
  rfl

/-- The three fields of `modulusPhaseMonicCubicRoots a b c` are exactly the
solutions of `x^3 + a*x^2 + b*x + c = 0`, for arbitrary complex coefficients,
including repeated and triple roots. -/
theorem cardano_formula_modulusPhase_monic (a b c x : ℂ) :
    x ^ 3 + a * x ^ 2 + b * x + c = 0 ↔
      x = (modulusPhaseMonicCubicRoots a b c).x₀ ∨
      x = (modulusPhaseMonicCubicRoots a b c).x₁ ∨
      x = (modulusPhaseMonicCubicRoots a b c).x₂ := by
  have h := cardano_formula_modulusPhase one_ne_zero a b c x
  rwa [modulusPhaseCubicRoots_one, one_mul] at h

end CubicEquation.CardanoComplex
