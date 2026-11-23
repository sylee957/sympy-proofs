module

public import SympyProofs.CubicEquation.CardanoComplex.ModifiedConjugateCorrected.Formula

/-!
# Cardano's formula with the second radical given by modulus and phase

Take `u = modifiedPrincipal A`. When `u ≠ 0` the second radical has to be
`-p / (3 * u)`. Its modulus is the real cube root of `|B|` and its phase is the
phase of `-p * conj u`, so it is written here as their product, with no
division by `u`. When `u = 0` that product vanishes, `p = 0` and `B = -q`, and
a second term supplies `modifiedPrincipal (-q)`.

`modulusPhaseCubicRoots a b c d` computes the three solutions this way for
arbitrary complex coefficients, and `cardano_formula_modulusPhase` states that
they are exactly the solutions. The second radical equals the one of the
modified conjugate-corrected formula, by
`modulusPhaseV_eq_modifiedConjugateCorrectedV`, so the two formulas return the
same solutions in the same order.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open Complex
open scoped ComplexConjugate

/-! ### The complex sign -/

/-- The complex sign `z / |z|`. Its value at zero is zero. -/
def unitPhase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem unitPhase_zero : unitPhase 0 = 0 := by simp [unitPhase]

theorem norm_unitPhase {z : ℂ} (hz : z ≠ 0) : ‖unitPhase z‖ = 1 := by
  have h : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [unitPhase, norm_div, Complex.norm_real, norm_norm, div_self h]

/-! ### The second radical -/

/-- The second Cardano radical: the real cube root of `|B|` times the phase of
`-p * conj u`, plus a term that is nonzero only when `A = 0`. -/
def modulusPhaseV (p q : ℂ) : ℂ :=
  ((‖radicandMinus p q‖ ^ (3⁻¹ : ℝ) : ℝ) : ℂ) *
      unitPhase (-p * conj (modifiedPrincipal (radicandPlus p q))) +
    ((1 - ‖unitPhase (radicandPlus p q)‖ : ℝ) : ℂ) * modifiedPrincipal (-q)

/-- The modulus of the second radical times the modulus of the first is `|p| / 3`. -/
theorem norm_radicandMinus_rpow_mul (p q : ℂ) :
    ‖radicandMinus p q‖ ^ (3⁻¹ : ℝ) * ‖modifiedPrincipal (radicandPlus p q)‖ = ‖p‖ / 3 := by
  have ht : (‖radicandMinus p q‖ ^ (3⁻¹ : ℝ)) ^ 3 = ‖radicandMinus p q‖ :=
    Real.rpow_inv_natCast_pow (norm_nonneg _) (by decide : 3 ≠ 0)
  have hN : ‖modifiedPrincipal (radicandPlus p q)‖ ^ 3 = ‖radicandPlus p q‖ := by
    rw [← norm_pow, modifiedPrincipal_cube]
  have hC : ‖radicandPlus p q‖ * ‖radicandMinus p q‖ = (‖p‖ / 3) ^ 3 := by
    rw [← norm_mul, radicands_product, norm_pow, norm_div, norm_neg]
    norm_num
  refine (pow_left_inj₀ (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    (by positivity) (three_ne_zero)).mp ?_
  rw [mul_pow, ht, hN, mul_comm, hC]

/-- The modulus-and-phase expression is the usual pairing rule: the second
modified principal radical when the first radical is zero, and `-p / (3 * u)`
otherwise. -/
theorem modulusPhaseV_eq (p q : ℂ) :
    modulusPhaseV p q =
      if modifiedConjugateCorrectedU p q = 0 then modifiedPrincipal (radicandMinus p q)
      else (-p / 3) / modifiedConjugateCorrectedU p q := by
  have hu3 : modifiedPrincipal (radicandPlus p q) ^ 3 = radicandPlus p q :=
    modifiedPrincipal_cube _
  rw [modifiedConjugateCorrectedU]
  by_cases hu : modifiedPrincipal (radicandPlus p q) = 0
  · have hA : radicandPlus p q = 0 := by rw [← hu3, hu]; simp
    have hB : radicandMinus p q = -q := by
      have h := radicands_sum p q
      rwa [hA, zero_add] at h
    rw [ite_eq_left hu, modulusPhaseV, hu, hA, hB]
    simp
  · have hA : radicandPlus p q ≠ 0 := fun hA => hu (by rw [hA, modifiedPrincipal_zero])
    rw [ite_eq_right hu, modulusPhaseV, norm_unitPhase hA, sub_self, ofReal_zero, zero_mul,
      add_zero]
    by_cases hp : p = 0
    · simp [hp]
    · have hkey := norm_radicandMinus_rpow_mul p q
      have hnorm : ‖-p * conj (modifiedPrincipal (radicandPlus p q))‖ =
          ‖p‖ * ‖modifiedPrincipal (radicandPlus p q)‖ := by
        rw [norm_mul, norm_neg, Complex.norm_conj]
      have hden : ((‖p‖ * ‖modifiedPrincipal (radicandPlus p q)‖ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast mul_ne_zero (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hu)
      have hconj := Complex.conj_mul' (modifiedPrincipal (radicandPlus p q))
      have hkeyC : ((‖radicandMinus p q‖ ^ (3⁻¹ : ℝ) : ℝ) : ℂ) *
          ((‖modifiedPrincipal (radicandPlus p q)‖ : ℝ) : ℂ) = ((‖p‖ : ℝ) : ℂ) / 3 := by
        exact_mod_cast hkey
      rw [unitPhase, hnorm, ← mul_div_assoc, div_eq_div_iff hden hu]
      push_cast
      linear_combination
        (-((‖radicandMinus p q‖ ^ (3⁻¹ : ℝ) : ℝ) : ℂ) * p) * hconj +
          (-p * ((‖modifiedPrincipal (radicandPlus p q)‖ : ℝ) : ℂ)) * hkeyC

/-- The second radical is the one of the modified conjugate-corrected formula. -/
theorem modulusPhaseV_eq_modifiedConjugateCorrectedV (p q : ℂ) :
    modulusPhaseV p q = modifiedConjugateCorrectedV p q := by
  rw [modulusPhaseV_eq, modifiedConjugateCorrectedV, conjugatePairedRoot_eq]

/-- Both Cardano pairing identities hold, including when either radical is zero. -/
theorem modulusPhase_pair (p q : ℂ) :
    modulusPhaseV p q ^ 3 = radicandMinus p q ∧
      modifiedConjugateCorrectedU p q * modulusPhaseV p q = -p / 3 := by
  rw [modulusPhaseV_eq_modifiedConjugateCorrectedV]
  exact modifiedConjugateCorrected_pair p q

/-! ### The formula -/

/-- The three Cardano solutions of the complex cubic `a*x^3 + b*x^2 + c*x + d = 0`.
The first radical `u` is a modified principal cube root. The second radical `v`
is built from a real cube root of a modulus and a complex sign, and no radical
is used as a denominator. -/
def modulusPhaseCubicRoots (a b c d : ℂ) : CardanoRoots :=
  let p := c / a - (b / a) ^ 2 / 3
  let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let Δ := q ^ 2 / 4 + p ^ 3 / 27
  let A := -q / 2 + Complex.sqrt Δ
  let B := -q / 2 - Complex.sqrt Δ
  let u := modifiedPrincipal A
  let v := ((‖B‖ ^ (3⁻¹ : ℝ) : ℝ) : ℂ) * unitPhase (-p * conj u) +
    ((1 - ‖unitPhase A‖ : ℝ) : ℂ) * modifiedPrincipal (-q)
  let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
  let shift := (b / a) / 3
  { x₀ := u + v - shift
    x₁ := ω * u + ω ^ 2 * v - shift
    x₂ := ω ^ 2 * u + ω * v - shift }

theorem modulusPhaseCubicRoots_x₀_eq (a b c d : ℂ) :
    (modulusPhaseCubicRoots a b c d).x₀ =
      modifiedConjugateCorrectedU (depressedP a b c) (depressedQ a b c d) +
        modulusPhaseV (depressedP a b c) (depressedQ a b c d) - (b / a) / 3 :=
  rfl

theorem modulusPhaseCubicRoots_x₁_eq (a b c d : ℂ) :
    (modulusPhaseCubicRoots a b c d).x₁ =
      omega * modifiedConjugateCorrectedU (depressedP a b c) (depressedQ a b c d) +
        omega ^ 2 * modulusPhaseV (depressedP a b c) (depressedQ a b c d) - (b / a) / 3 :=
  rfl

theorem modulusPhaseCubicRoots_x₂_eq (a b c d : ℂ) :
    (modulusPhaseCubicRoots a b c d).x₂ =
      omega ^ 2 * modifiedConjugateCorrectedU (depressedP a b c) (depressedQ a b c d) +
        omega * modulusPhaseV (depressedP a b c) (depressedQ a b c d) - (b / a) / 3 :=
  rfl

/-- The three fields of `modulusPhaseCubicRoots a b c d` are exactly the
solutions of `a*x^3 + b*x^2 + c*x + d = 0`, for arbitrary complex coefficients
with `a ≠ 0`, including repeated and triple roots. -/
theorem cardano_formula_modulusPhase {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = (modulusPhaseCubicRoots a b c d).x₀ ∨
      x = (modulusPhaseCubicRoots a b c d).x₁ ∨
      x = (modulusPhaseCubicRoots a b c d).x₂ := by
  rw [modulusPhaseCubicRoots_x₀_eq, modulusPhaseCubicRoots_x₁_eq, modulusPhaseCubicRoots_x₂_eq]
  have hpair := modulusPhase_pair (depressedP a b c) (depressedQ a b c d)
  apply cubic_formula_of_compatible_pair ha b c d x
  · rw [modifiedConjugateCorrectedU_cube, hpair.1, radicands_sum]
  · exact hpair.2

end CubicEquation.CardanoComplex
