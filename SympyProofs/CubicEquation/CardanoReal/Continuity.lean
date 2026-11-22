module

public import SympyProofs.CubicEquation.CardanoReal.ReIm.Order
public import SympyProofs.RealCubeRoot.ModifiedPrincipal.Analytic

/-!
# Continuity of the Cardano solutions in the coefficients

Each of the two functions has one field that is continuous in the coefficients
of the cubic wherever the leading coefficient is nonzero: the third field of
`modifiedPrincipalCubicRoots` and the second field of
`modifiedPrincipalCubicRootsReIm`.

The proof glues two expressions that are continuous on the whole coefficient
plane. For nonnegative discriminant the radicals are real cube roots of
continuous real radicands. For negative discriminant they are the principal
cube root of `upperRadicand p q` and its conjugate, and the principal cube
root is continuous on the closed upper half-plane. The two expressions agree
where the discriminant vanishes.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex Filter
open scoped Topology ComplexConjugate

/-! ### Continuity of the radicands -/

theorem continuous_realDiscriminant :
    Continuous fun x : ℝ × ℝ => realDiscriminant x.1 x.2 := by
  unfold realDiscriminant
  fun_prop

theorem continuous_realRadicandPlus :
    Continuous fun x : ℝ × ℝ => realRadicandPlus x.1 x.2 := by
  unfold realRadicandPlus realDiscriminant
  fun_prop

theorem continuous_realRadicandMinus :
    Continuous fun x : ℝ × ℝ => realRadicandMinus x.1 x.2 := by
  unfold realRadicandMinus realDiscriminant
  fun_prop

theorem continuous_upperRadicand :
    Continuous fun x : ℝ × ℝ => upperRadicand x.1 x.2 := by
  unfold upperRadicand realDiscriminant
  fun_prop

/-- The principal cube root of the upper radicand is continuous on the whole
coefficient plane, including where the radicand is a negative real. -/
theorem continuous_principal_upperRadicand :
    Continuous fun x : ℝ × ℝ => principal (upperRadicand x.1 x.2) :=
  continuousOn_principal_upper.comp_continuous continuous_upperRadicand
    fun x => upperRadicand_im_nonneg x.1 x.2

/-! ### Where the discriminant vanishes -/

/-- On every real input, the real cube root is recovered from the real and
imaginary parts of the principal cube root. -/
theorem principal_ofReal_re_sub (m : ℝ) :
    (principal (m : ℂ)).re - Real.sqrt 3 * (principal (m : ℂ)).im = realCubicSurd m := by
  have h := congrArg Complex.re (modifiedPrincipal_ofReal m)
  simp only [modifiedPrincipal, conj_ofReal, ofReal_re] at h
  rw [← h]
  simp [Complex.mul_re, show conj (2 : ℂ) = 2 from conj_ofReal 2]
  ring

private theorem real_values_eq_of_eq_zero {p q : ℝ} (h : realDiscriminant p q = 0) :
    omega ^ 2 * (realCubicSurd (realRadicandPlus p q) : ℂ) +
        omega * (realCubicSurd (realRadicandMinus p q) : ℂ) =
      omega ^ 2 * principal (upperRadicand p q) + omega * conj (principal (upperRadicand p q)) := by
  rw [omega_sq_mul_ofReal_add, omega_sq_mul_add_conj, realRadicandMinus_eq h,
    realRadicandPlus_of_eq_zero h, upperRadicand_of_eq_zero h, ← principal_ofReal_re_sub]
  push_cast
  ring

private theorem real_values_eq_of_eq_zero' {p q : ℝ} (h : realDiscriminant p q = 0) :
    omega * (realCubicSurd (realRadicandPlus p q) : ℂ) +
        omega ^ 2 * (realCubicSurd (realRadicandMinus p q) : ℂ) =
      omega ^ 2 * principal (upperRadicand p q) + omega * conj (principal (upperRadicand p q)) := by
  rw [← real_values_eq_of_eq_zero h, omega_mul_ofReal_add, omega_sq_mul_ofReal_add,
    realRadicandMinus_eq h]
  simp

/-! ### Depressed coefficients -/

/-- The third Cardano value is continuous on the whole coefficient plane. -/
theorem continuous_omega_sq_mul_modifiedU_add :
    Continuous fun x : ℝ × ℝ => omega ^ 2 * modifiedU x.1 x.2 + omega * modifiedV x.1 x.2 := by
  have hG : Continuous fun x : ℝ × ℝ =>
      omega ^ 2 * (realCubicSurd (realRadicandPlus x.1 x.2) : ℂ) +
        omega * (realCubicSurd (realRadicandMinus x.1 x.2) : ℂ) :=
    (continuous_const.mul
      (continuous_ofReal.comp (continuous_realCubicSurd.comp continuous_realRadicandPlus))).add
    (continuous_const.mul
      (continuous_ofReal.comp (continuous_realCubicSurd.comp continuous_realRadicandMinus)))
  have hH : Continuous fun x : ℝ × ℝ =>
      omega ^ 2 * principal (upperRadicand x.1 x.2) +
        omega * conj (principal (upperRadicand x.1 x.2)) :=
    (continuous_const.mul continuous_principal_upperRadicand).add
      (continuous_const.mul (continuous_conj.comp continuous_principal_upperRadicand))
  have key := Continuous.if_le hG hH continuous_const continuous_realDiscriminant
    fun x (hx : (0 : ℝ) = realDiscriminant x.1 x.2) => real_values_eq_of_eq_zero hx.symm
  refine key.congr fun x => ?_
  split_ifs with h
  · rw [modifiedU_of_nonneg h, modifiedV_of_nonneg h]
  · rw [modifiedU_of_neg (not_le.mp h), modifiedV_of_neg (not_le.mp h)]

/-- The root of the quadratic factor taken with the plus sign is continuous on
the whole coefficient plane. -/
theorem continuous_quadratic_plus :
    Continuous fun x : ℝ × ℝ =>
      (-(principalRealRoot x.1 x.2 : ℂ) +
        Complex.sqrt (-3 * (principalRealRoot x.1 x.2 : ℂ) ^ 2 - 4 * (x.1 : ℂ))) / 2 := by
  have hG : Continuous fun x : ℝ × ℝ =>
      omega * (realCubicSurd (realRadicandPlus x.1 x.2) : ℂ) +
        omega ^ 2 * (realCubicSurd (realRadicandMinus x.1 x.2) : ℂ) :=
    (continuous_const.mul
      (continuous_ofReal.comp (continuous_realCubicSurd.comp continuous_realRadicandPlus))).add
    (continuous_const.mul
      (continuous_ofReal.comp (continuous_realCubicSurd.comp continuous_realRadicandMinus)))
  have hH : Continuous fun x : ℝ × ℝ =>
      omega ^ 2 * principal (upperRadicand x.1 x.2) +
        omega * conj (principal (upperRadicand x.1 x.2)) :=
    (continuous_const.mul continuous_principal_upperRadicand).add
      (continuous_const.mul (continuous_conj.comp continuous_principal_upperRadicand))
  have key := Continuous.if_le hG hH continuous_const continuous_realDiscriminant
    fun x (hx : (0 : ℝ) = realDiscriminant x.1 x.2) => real_values_eq_of_eq_zero' hx.symm
  refine key.congr fun x => ?_
  split_ifs with h
  · rw [quadratic_plus_of_nonneg h, modifiedU_of_nonneg h, modifiedV_of_nonneg h]
  · rw [quadratic_plus_of_neg (not_le.mp h), modifiedU_of_neg (not_le.mp h),
      modifiedV_of_neg (not_le.mp h)]

/-! ### General coefficients -/

private theorem continuousOn_depressed :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ =>
      (realDepressedP x.1 x.2.1 x.2.2.1, realDepressedQ x.1 x.2.1 x.2.2.1 x.2.2.2))
      {x | x.1 ≠ 0} := by
  unfold realDepressedP realDepressedQ
  fun_prop (disch := intro x hx; first | exact hx | norm_num)

private theorem continuousOn_shift :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ => ((x.2.1 / x.1 / 3 : ℝ) : ℂ)) {x | x.1 ≠ 0} := by
  fun_prop (disch := intro x hx; first | exact hx | norm_num)

/-- The third solution of `modifiedPrincipalCubicRoots` is continuous in the
four coefficients wherever the leading coefficient is nonzero. -/
theorem continuousOn_modifiedPrincipalCubicRoots_x₂ :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ =>
      (modifiedPrincipalCubicRoots x.1 x.2.1 x.2.2.1 x.2.2.2).x₂) {x | x.1 ≠ 0} := by
  simp only [modifiedPrincipalCubicRoots_x₂_eq]
  exact (continuous_omega_sq_mul_modifiedU_add.comp_continuousOn continuousOn_depressed).sub
    continuousOn_shift

/-- The second solution of `modifiedPrincipalCubicRootsReIm` is continuous in
the four coefficients wherever the leading coefficient is nonzero. -/
theorem continuousOn_modifiedPrincipalCubicRootsReIm_x₁ :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ =>
      (modifiedPrincipalCubicRootsReIm x.1 x.2.1 x.2.2.1 x.2.2.2).x₁) {x | x.1 ≠ 0} := by
  simp only [modifiedPrincipalCubicRootsReIm_x₁_eq]
  exact (continuous_quadratic_plus.comp_continuousOn continuousOn_depressed).sub
    continuousOn_shift

end CubicEquation.CardanoReal
