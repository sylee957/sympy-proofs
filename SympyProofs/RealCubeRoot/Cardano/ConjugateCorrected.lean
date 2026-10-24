module

public import SympyProofs.RealCubeRoot.Cardano.Principal

/-!
# Cardano's formula with a conjugation-based zero detector

Write `P` for the principal cube root and define
`E(r) = (P(-1 + r*i) - conj (P(-1 - r*i))) / (i*sqrt(3))`.
For real `r`, conjugation makes the numerator zero unless `r = 0`.
At zero, the principal branch values at `-1` instead give `E(0) = 1`.
Both detector inputs are nonzero for every real `r`.

Given the Cardano radicands `A`, `B` and `C = -p/3`, let `U = P(A)`,
`W = P(B)`, and `r = U * conj U`. Then
`V = (C * conj U + E(r) * W) / (r + E(r))`
is the compatible second cube root. The denominator is a positive real number,
including when `U = 0`. This expression equals the usual paired principal
construction, so it gives the same ordered roots and their multiplicities.

The displayed formula uses only principal radicals, conjugation, and arithmetic.
There are no explicit conditionals, argument calls, rounding, or sign functions;
the principal branch cut encodes the zero test. See `cardano_formula_conjugateCorrected`
for the complete formula with all intermediate quantities visible.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- An ambient complex expression which detects zero on real inputs.
Its values at general nonreal inputs are not asserted to be a zero indicator. -/
def conjugateZeroDetector (r : ℂ) : ℂ :=
  (principal (-1 + r * I) - conj (principal (-1 - r * I))) /
    (I * (Real.sqrt 3 : ℂ))

theorem conjugateZeroDetector_divisor_ne_zero : I * (Real.sqrt 3 : ℂ) ≠ 0 := by
  apply mul_ne_zero I_ne_zero
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))

/-- The principal cube root at `-1` has imaginary part `sqrt(3)/2`;
its difference from its conjugate yields the detector value one. -/
@[simp] theorem conjugateZeroDetector_zero : conjugateZeroDetector 0 = 1 := by
  have hP : principal (-1 : ℂ) = (1 + (Real.sqrt 3 : ℂ) * I) / 2 := by
    simpa using principal_ofReal_of_neg (by norm_num : (-1 : ℝ) < 0)
  simp only [conjugateZeroDetector, zero_mul, add_zero, sub_zero, hP,
    map_div₀, map_add, map_one, map_mul, conj_ofReal, conj_I,
    show conj (2 : ℂ) = 2 from conj_ofReal 2]
  apply (div_eq_iff conjugateZeroDetector_divisor_ne_zero).mpr
  ring

/-- For a nonzero real input, both radicals lie off the branch cut and their
conjugation identity makes the detector vanish. -/
theorem conjugateZeroDetector_ofReal_ne_zero {r : ℝ} (hr : r ≠ 0) :
    conjugateZeroDetector (r : ℂ) = 0 := by
  have hz : (-1 - (r : ℂ) * I) ∈ slitPlane := by
    apply Or.inr
    simpa using (neg_ne_zero.mpr hr)
  have hc : conj (-1 - (r : ℂ) * I) = -1 + (r : ℂ) * I := by
    simp
  rw [conjugateZeroDetector, ← principal_conj_of_mem_slitPlane hz, hc, sub_self, zero_div]

/-- The exact zero-test behavior on the real line. -/
theorem conjugateZeroDetector_ofReal (r : ℝ) :
    conjugateZeroDetector (r : ℂ) = if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · simp [hr]
  · simp [hr, conjugateZeroDetector_ofReal_ne_zero hr]

/-- The detector never needs a principal-root input at zero. -/
theorem conjugateZeroDetector_inputs_ne_zero (r : ℝ) :
    (-1 + (r : ℂ) * I) ≠ 0 ∧ (-1 - (r : ℂ) * I) ≠ 0 := by
  constructor <;> intro h <;> have h' := congrArg Complex.re h <;> norm_num at h'

theorem conjugatePairedRoot_denominator_im (U : ℂ) :
    (U * conj U + conjugateZeroDetector (U * conj U)).im = 0 := by
  rw [mul_conj, conjugateZeroDetector_ofReal]
  split_ifs <;> simp

/-- The variable denominator is strictly positive, even when the first radical is zero. -/
theorem conjugatePairedRoot_denominator_re_pos (U : ℂ) :
    0 < (U * conj U + conjugateZeroDetector (U * conj U)).re := by
  rw [mul_conj]
  by_cases hU : U = 0
  · simp [hU]
  · have hr : 0 < normSq U := normSq_pos.mpr hU
    rw [conjugateZeroDetector_ofReal_ne_zero hr.ne', add_zero, ofReal_re]
    exact hr

theorem conjugatePairedRoot_denominator_ne_zero (U : ℂ) :
    U * conj U + conjugateZeroDetector (U * conj U) ≠ 0 := by
  intro h
  have := conjugatePairedRoot_denominator_re_pos U
  simp [h] at this

/-- Pair a first radical `U` with the target product `C`, using `W` at zero.
The displayed definition has no conditionals and its denominator never vanishes. -/
def conjugatePairedRoot (U W C : ℂ) : ℂ :=
  let r := U * conj U
  let e := conjugateZeroDetector r
  (C * conj U + e * W) / (r + e)

/-- The conjugation expression exactly implements the usual pairing rule. -/
theorem conjugatePairedRoot_eq (U W C : ℂ) :
    conjugatePairedRoot U W C = if U = 0 then W else C / U := by
  by_cases hU : U = 0
  · simp [conjugatePairedRoot, hU]
  · have hr : normSq U ≠ 0 := (normSq_pos.mpr hU).ne'
    have he : conjugateZeroDetector (U * conj U) = 0 := by
      rw [mul_conj, conjugateZeroDetector_ofReal_ne_zero hr]
    have hc : conj U ≠ 0 := by simpa using hU
    simp only [conjugatePairedRoot, he, zero_mul, add_zero, hU, ↓reduceIte]
    field_simp

/-- Pairing leaves an already compatible second radical unchanged, including at zero. -/
theorem conjugatePairedRoot_eq_of_mul_eq {U W C : ℂ} (h : U * W = C) :
    conjugatePairedRoot U W C = W := by
  rw [conjugatePairedRoot_eq]
  by_cases hU : U = 0
  · simp [hU]
  · rw [ite_eq_right hU]
    apply (div_eq_iff hU).mpr
    rw [← h]
    ring

/-- Correct any pair of cube roots whose cubes have the required product. -/
theorem conjugatePairedRoot_spec {U W C : ℂ} (h : U ^ 3 * W ^ 3 = C ^ 3) :
    conjugatePairedRoot U W C ^ 3 = W ^ 3 ∧
      U * conjugatePairedRoot U W C = C := by
  by_cases hU : U = 0
  · have hC : C = 0 := by simpa [hU] using h.symm
    simp [conjugatePairedRoot_eq, hU, hC]
  · have hprod : U * conjugatePairedRoot U W C = C := by
      rw [conjugatePairedRoot_eq, ite_eq_right hU]
      field_simp
    refine ⟨?_, hprod⟩
    apply mul_left_cancel₀ (pow_ne_zero 3 hU)
    calc
      U ^ 3 * conjugatePairedRoot U W C ^ 3 =
          (U * conjugatePairedRoot U W C) ^ 3 := (mul_pow _ _ _).symm
      _ = C ^ 3 := by rw [hprod]
      _ = U ^ 3 * W ^ 3 := h.symm

/-- Cardano's second radical, expressed using the conjugation-based detector. -/
def conjugateCorrectedV (p q : ℂ) : ℂ :=
  conjugatePairedRoot (u p q) (principal (radicandMinus p q)) (-p / 3)

theorem conjugateCorrectedV_eq_v (p q : ℂ) : conjugateCorrectedV p q = v p q := by
  simp only [conjugateCorrectedV, conjugatePairedRoot_eq, v, div_div]

@[simp] theorem conjugateCorrectedV_cube (p q : ℂ) :
    conjugateCorrectedV p q ^ 3 = radicandMinus p q := by
  rw [conjugateCorrectedV_eq_v, v_cube]

theorem conjugateCorrected_uv (p q : ℂ) : u p q * conjugateCorrectedV p q = -p / 3 := by
  rw [conjugateCorrectedV_eq_v, uv]

/-- Exact factorization, including repeated and triple roots. -/
theorem conjugateCorrected_depressed_factorization (p q x : ℂ) :
    (x - (u p q + conjugateCorrectedV p q)) *
      (x - (omega * u p q + omega ^ 2 * conjugateCorrectedV p q)) *
      (x - (omega ^ 2 * u p q + omega * conjugateCorrectedV p q)) =
        x ^ 3 + p * x + q := by
  simpa only [conjugateCorrectedV_eq_v] using depressed_factorization p q x

/-- Cardano's formula for arbitrary complex coefficients using only principal
radicals, conjugation, and arithmetic. The divisor in `E` is nonzero, and the
variable denominator `r + e` is positive real by the denominator theorems above. -/
theorem cardano_formula_conjugateCorrected {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
    let E : ℂ → ℂ := fun r =>
      (principal (-1 + r * I) - conj (principal (-1 - r * I))) /
        (I * (Real.sqrt 3 : ℂ))
    let u := principal A
    let w := principal B
    let r := u * conj u
    let e := E r
    let v := (C * conj u + e * w) / (r + e)
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  simpa only [cubicRoots, depressedRoots, pairedRoots, ← conjugateCorrectedV_eq_v,
    conjugateCorrectedV, conjugatePairedRoot, conjugateZeroDetector, u,
    radicandPlus, radicandMinus, discriminant, depressedP, depressedQ, omega,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using
    (mem_cubicRoots_iff ha b c d x).symm

end RealCubeRoot.Cardano
