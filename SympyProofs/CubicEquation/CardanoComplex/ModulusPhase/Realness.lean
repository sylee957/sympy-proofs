module

public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Monic
public import SympyProofs.CubicEquation.CardanoComplex.ModifiedConjugateCorrected.Realness
public import SympyProofs.CubicEquation.CardanoReal.ModifiedPrincipal.Shortcuts

/-!
# The modulus-and-phase formula on real coefficients

For real coefficients the second radical of the modulus-and-phase formula is
the second modified principal radical. So `modulusPhaseCubicRoots` equals
`modifiedPrincipalCubicRoots`, field by field, and its first solution is real.

The same holds for the monic formulas. Hence, for a real monic cubic whose
discriminant has a known sign, `modulusPhaseMonicCubicRoots` equals the
simpler formulas of `CardanoReal/ModifiedPrincipal/Shortcuts.lean`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open CardanoReal
open Complex
open scoped ComplexConjugate

/-- For real coefficients, the second radical is the second modified principal radical. -/
theorem modulusPhaseV_ofReal (p q : ℝ) :
    modulusPhaseV (p : ℂ) q = modifiedPrincipal (radicandMinus (p : ℂ) q) := by
  rw [modulusPhaseV_eq_modifiedConjugateCorrectedV, modifiedConjugateCorrectedV_ofReal]

/-- For real coefficients the formula is the modified-principal formula, with
the three solutions in the same order. -/
theorem modulusPhaseCubicRoots_ofReal (a b c d : ℝ) :
    modulusPhaseCubicRoots (a : ℂ) b c d = modifiedPrincipalCubicRoots a b c d := by
  have hshift : ((b : ℂ) / a) / 3 = ((b / a / 3 : ℝ) : ℂ) := by push_cast; ring
  have hP : depressedP (a : ℂ) b c = (realDepressedP a b c : ℝ) := depressedP_ofReal a b c
  have hQ : depressedQ (a : ℂ) b c d = (realDepressedQ a b c d : ℝ) :=
    depressedQ_ofReal a b c d
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseCubicRoots_x₀_eq, modifiedPrincipalCubicRoots_x₀_eq, hP, hQ,
      modulusPhaseV_ofReal, hshift]
    rfl
  · rw [modulusPhaseCubicRoots_x₁_eq, modifiedPrincipalCubicRoots_x₁_eq, hP, hQ,
      modulusPhaseV_ofReal, hshift]
    rfl
  · rw [modulusPhaseCubicRoots_x₂_eq, modifiedPrincipalCubicRoots_x₂_eq, hP, hQ,
      modulusPhaseV_ofReal, hshift]
    rfl

/-- For real coefficients the first solution is real. -/
theorem modulusPhaseCubicRoots_x₀_im (a b c d : ℝ) :
    (modulusPhaseCubicRoots (a : ℂ) b c d).x₀.im = 0 := by
  rw [modulusPhaseCubicRoots_ofReal]
  exact modifiedPrincipal_cardano_first_im a b c d

/-! ### The monic formula -/

theorem complexMonicDepressedP_ofReal (a b : ℝ) :
    complexMonicDepressedP (a : ℂ) b = (monicDepressedP a b : ℝ) := by
  simp [complexMonicDepressedP, monicDepressedP]

theorem complexMonicDepressedQ_ofReal (a b c : ℝ) :
    complexMonicDepressedQ (a : ℂ) b c = (monicDepressedQ a b c : ℝ) := by
  simp [complexMonicDepressedQ, monicDepressedQ]

/-- For real coefficients the monic formula is the monic modified-principal
formula, with the three solutions in the same order. -/
theorem modulusPhaseMonicCubicRoots_ofReal (a b c : ℝ) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c = modifiedPrincipalMonicCubicRoots a b c := by
  have hshift : (a : ℂ) / 3 = ((a / 3 : ℝ) : ℂ) := by push_cast; ring
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, modifiedPrincipalMonicCubicRoots_x₀_eq,
      complexMonicDepressedP_ofReal, complexMonicDepressedQ_ofReal, modulusPhaseV_ofReal, hshift]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, modifiedPrincipalMonicCubicRoots_x₁_eq,
      complexMonicDepressedP_ofReal, complexMonicDepressedQ_ofReal, modulusPhaseV_ofReal, hshift]
    rfl
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, modifiedPrincipalMonicCubicRoots_x₂_eq,
      complexMonicDepressedP_ofReal, complexMonicDepressedQ_ofReal, modulusPhaseV_ofReal, hshift]
    rfl

/-- For real coefficients the first solution of the monic formula is real. -/
theorem modulusPhaseMonicCubicRoots_x₀_im (a b c : ℝ) :
    (modulusPhaseMonicCubicRoots (a : ℂ) b c).x₀.im = 0 := by
  rw [← modulusPhaseCubicRoots_one]
  exact_mod_cast modulusPhaseCubicRoots_x₀_im 1 a b c

/-- For real coefficients and nonnegative discriminant the formula needs only
real cube roots. -/
theorem modulusPhaseMonicCubicRoots_eq_realRadical {a b c : ℝ}
    (h : 0 ≤ monicCubicDiscriminant a b c) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c = realRadicalMonicCubicRoots a b c := by
  rw [modulusPhaseMonicCubicRoots_ofReal, modifiedPrincipalMonicCubicRoots_eq_realRadical h]

/-- For real coefficients and negative discriminant the formula needs only one
principal cube root. -/
theorem modulusPhaseMonicCubicRoots_eq_singleRadical {a b c : ℝ}
    (h : monicCubicDiscriminant a b c < 0) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c = singleRadicalMonicCubicRoots a b c := by
  rw [modulusPhaseMonicCubicRoots_ofReal, modifiedPrincipalMonicCubicRoots_eq_singleRadical h]

/-- For real coefficients and zero discriminant the formula needs no radical. -/
theorem modulusPhaseMonicCubicRoots_eq_repeatedRoot {a b c : ℝ}
    (h : monicCubicDiscriminant a b c = 0) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c = repeatedRootMonicCubicRoots a b c := by
  rw [modulusPhaseMonicCubicRoots_ofReal, modifiedPrincipalMonicCubicRoots_eq_repeatedRoot h]

end CubicEquation.CardanoComplex
