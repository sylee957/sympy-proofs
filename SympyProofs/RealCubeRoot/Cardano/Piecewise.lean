module

public import SympyProofs.RealCubeRoot.Cardano.ModifiedPrincipal
public import SympyProofs.RealCubeRoot.Cardano.PhaseCorrected
public import SympyProofs.RealCubeRoot.Cardano.ConjugateCorrected

/-!
# Cardano's formula with explicit piecewise principal-root corrections

For real coefficients, `piecewisePrincipal` changes the principal cube root
only on the negative real axis. It equals `modifiedPrincipal`, so the symmetric
formula has an always-real first root.

For arbitrary complex coefficients, `piecewisePhase` chooses one of `1`, `omega`,
and `omega ^ 2` to pair the two principal radicals. On Cardano inputs it equals
the sign-based phase correction. The resulting second radical also equals the
usual rule `if U = 0 then W else C / U`, and hence the conjugation-based formula.
All comparisons preserve the ordered three expressions, including repeated roots.

The complete formulas appear in `cardano_formula_piecewise_real` and
`cardano_formula_piecewise_complex`, with each conditional visible.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

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
  simpa only [piecewisePrincipal_eq_modifiedPrincipal] using
    modifiedPrincipal_cardano_first_im a b c d

/-- An explicit three-way phase choice. At zero the chosen factor is `1`.
Only its values on the three cube-root rays are needed for Cardano. -/
def piecewisePhase (Z : ℂ) : ℂ :=
  if 0 ≤ Z.re then 1 else if 0 ≤ Z.im then omega else omega ^ 2

@[simp] theorem piecewisePhase_ofReal {r : ℝ} (hr : 0 ≤ r) :
    piecewisePhase (r : ℂ) = 1 := by
  simp [piecewisePhase, hr]

theorem piecewisePhase_omega_mul {r : ℝ} (hr : 0 < r) :
    piecewisePhase (omega * r) = omega := by
  have hre : (omega * r).re < 0 := by
    simp [omega, Complex.mul_re]
    linarith
  have him : 0 < (omega * r).im := by
    simp [omega, Complex.mul_im]
    positivity
  simp only [piecewisePhase, not_le.mpr hre, him.le, ↓reduceIte]

theorem piecewisePhase_omega_sq_mul {r : ℝ} (hr : 0 < r) :
    piecewisePhase (omega ^ 2 * r) = omega ^ 2 := by
  have hre : (omega ^ 2 * r).re < 0 := by
    rw [omega_sq]
    simp [omega, Complex.mul_re]
    linarith
  have him : (omega ^ 2 * r).im < 0 := by
    rw [omega_sq]
    simp [omega, Complex.mul_im]
    have : 0 < Real.sqrt 3 * r := mul_pos (by positivity) hr
    nlinarith
  simp only [piecewisePhase, not_le.mpr hre, not_le.mpr him, ↓reduceIte]

/-- Agreement with the sign formula on every compatible cube-product input.
The restriction matters: the two selectors need not agree at arbitrary `Z`. -/
theorem piecewisePhase_eq_signPhase {W C : ℂ} (h : C ^ 3 = W ^ 3) :
    piecewisePhase (C * conj W) = omega ^ (signPhase (C * conj W) : ℂ) := by
  by_cases hW : W = 0
  · simp [hW, piecewisePhase, signPhase]
  · have hr : 0 < normSq W := normSq_pos.mpr hW
    rcases (cube_eq_cube_iff C W).mp h with rfl | rfl | rfl
    · rw [mul_conj, piecewisePhase_ofReal hr.le, signPhase_ofReal]
      simp
    · rw [mul_assoc, mul_conj, piecewisePhase_omega_mul hr, signPhase_omega_mul hr]
      simp
    · rw [mul_assoc, mul_conj, piecewisePhase_omega_sq_mul hr,
        signPhase_omega_sq_mul hr]
      simp only [ofReal_neg, ofReal_one, Complex.cpow_neg_one, omega_inv_eq_sq]

/-- The second radical with a visible finite phase selection. -/
def piecewiseCorrectedV (p q : ℂ) : ℂ :=
  let U := principal (radicandPlus p q)
  let W := principal (radicandMinus p q)
  let Z := (-p / 3) * conj (U * W)
  piecewisePhase Z * W

theorem piecewiseCorrectedV_eq_signCorrectedV (p q : ℂ) :
    piecewiseCorrectedV p q = signCorrectedV p q := by
  have hcube : (-p / 3) ^ 3 =
      (principal (radicandPlus p q) * principal (radicandMinus p q)) ^ 3 := by
    rw [mul_pow, principal_cube, principal_cube, radicands_product]
  simp only [piecewiseCorrectedV, signCorrectedV, piecewisePhase_eq_signPhase hcube]

theorem piecewiseCorrected_pair (p q : ℂ) :
    piecewiseCorrectedV p q ^ 3 = radicandMinus p q ∧
      u p q * piecewiseCorrectedV p q = -p / 3 := by
  rw [piecewiseCorrectedV_eq_signCorrectedV]
  exact signCorrected_pair p q

/-- The phase selection also equals the standard two-case quotient formula.
When `u = 0`, the phase input is zero and the second principal root is retained. -/
theorem piecewiseCorrectedV_eq_v (p q : ℂ) : piecewiseCorrectedV p q = v p q := by
  by_cases hu : u p q = 0
  · have hU : principal (radicandPlus p q) = 0 := hu
    simp [piecewiseCorrectedV, hU, hu, piecewisePhase, v]
  · rw [v, ite_eq_right hu]
    have hprod := (piecewiseCorrected_pair p q).2
    apply (eq_div_iff (mul_ne_zero (by norm_num) hu)).mpr
    calc
      piecewiseCorrectedV p q * (3 * u p q) =
          3 * (u p q * piecewiseCorrectedV p q) := by ring
      _ = -p := by rw [hprod]; ring

/-- The piecewise and conjugation-based formulas give identical ordered roots. -/
theorem piecewiseCorrectedV_eq_conjugateCorrectedV (p q : ℂ) :
    piecewiseCorrectedV p q = conjugateCorrectedV p q := by
  rw [piecewiseCorrectedV_eq_v, conjugateCorrectedV_eq_v]

/-- Arbitrary complex coefficients: correct the second principal radical by
one of three explicitly selected phases. No radical is used as a denominator. -/
theorem cardano_formula_piecewise_complex {a : ℂ} (ha : a ≠ 0) (b c d x : ℂ) :
    let p := c / a - (b / a) ^ 2 / 3
    let q := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ := q ^ 2 / 4 + p ^ 3 / 27
    let A := -q / 2 + Complex.sqrt Δ
    let B := -q / 2 - Complex.sqrt Δ
    let C := -p / 3
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2
    let u := principal A
    let w := principal B
    let Z := C * conj (u * w)
    let v := if 0 ≤ Z.re then w else if 0 ≤ Z.im then ω * w else ω ^ 2 * w
    let shift := (b / a) / 3
    let x₀ := u + v - shift
    let x₁ := ω * u + ω ^ 2 * v - shift
    let x₂ := ω ^ 2 * u + ω * v - shift
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔ x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  let p := depressedP a b c
  let q := depressedQ a b c d
  have hpair := piecewiseCorrected_pair p q
  have hsum : u p q ^ 3 + piecewiseCorrectedV p q ^ 3 = -q := by
    rw [u_cube, hpair.1, radicands_sum]
  simpa only [p, q, u, piecewiseCorrectedV, piecewisePhase, radicandPlus, radicandMinus,
    discriminant, depressedP, depressedQ, omega, ite_mul, one_mul] using
    (cubic_formula_of_compatible_pair ha b c d x (u p q) (piecewiseCorrectedV p q)
      hsum hpair.2)

end RealCubeRoot.Cardano
