module

public import SympyProofs.CubicEquation.CardanoReal.Continuity

/-!
# The jump of the first Cardano solution

Consider depressed cubics `x^3 + p*x + q`, and a point `(p, q)` with zero
discriminant and `0 < q`. There the double root lies above the simple root.
Approach the point through cubics with negative discriminant, that is, with
three distinct real roots.

* For `modifiedPrincipalCubicRoots`, the first field tends to the value of the
  second field at the point, and the second field tends to the value of the
  first. The two values differ, so neither field is continuous there.
* For `modifiedPrincipalCubicRootsReIm`, the same holds with the third field
  in place of the second.

The remaining field of each function is continuous everywhere, as shown in
`Continuity.lean`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoReal

open RealCubeRoot
open CardanoComplex
open Complex Filter
open scoped Topology ComplexConjugate

/-! ### Approaching zero discriminant from the negative side -/

/-- Every point of zero discriminant is a limit of points of negative discriminant. -/
theorem neBot_nhdsWithin_discriminant_neg {p q : ℝ} (hΔ : realDiscriminant p q = 0) :
    (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(p - ε / 2, q), ?_, ?_⟩
  · have h3 : (p - ε / 2) ^ 3 < p ^ 3 :=
      (show Odd (3 : ℕ) by decide).strictMono_pow (by linarith)
    change realDiscriminant (p - ε / 2) q < 0
    unfold realDiscriminant at hΔ ⊢
    linarith
  · rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq, sub_sub_cancel, abs_of_pos (half_pos hε)]
    exact max_lt (half_lt_self hε) hε

/-! ### Values at a point of zero discriminant -/

private theorem modifiedU_of_eq_zero {p q : ℝ} (hΔ : realDiscriminant p q = 0) :
    modifiedU p q = (realCubicSurd (-q / 2) : ℂ) := by
  rw [modifiedU_of_nonneg hΔ.ge, realRadicandPlus_of_eq_zero hΔ]

private theorem modifiedV_of_eq_zero {p q : ℝ} (hΔ : realDiscriminant p q = 0) :
    modifiedV p q = (realCubicSurd (-q / 2) : ℂ) := by
  rw [modifiedV_of_nonneg hΔ.ge, realRadicandMinus_eq hΔ, realRadicandPlus_of_eq_zero hΔ]

private theorem principal_ofReal_of_neg_eq {m : ℝ} (hm : m < 0) :
    principal (m : ℂ) = ((-realCubicSurd m / 2 : ℝ) : ℂ) +
      ((-(Real.sqrt 3 * realCubicSurd m) / 2 : ℝ) : ℂ) * I := by
  rw [principal_ofReal_of_neg hm]
  simp only [realCubicSurd, hm, ↓reduceIte]
  push_cast
  ring

private theorem principal_upperRadicand_re {p q : ℝ} (hΔ : realDiscriminant p q = 0)
    (hq : 0 < q) :
    (principal (upperRadicand p q)).re = -realCubicSurd (-q / 2) / 2 := by
  rw [upperRadicand_of_eq_zero hΔ, principal_ofReal_of_neg_eq (by linarith)]
  simp

private theorem principal_upperRadicand_im {p q : ℝ} (hΔ : realDiscriminant p q = 0)
    (hq : 0 < q) :
    (principal (upperRadicand p q)).im = -(Real.sqrt 3 * realCubicSurd (-q / 2)) / 2 := by
  rw [upperRadicand_of_eq_zero hΔ, principal_ofReal_of_neg_eq (by linarith)]
  simp

/-! ### Depressed coefficients -/

/-- Approaching through negative discriminant, the first Cardano value tends
to the second Cardano value of the limit point. -/
theorem tendsto_modifiedU_add_modifiedV_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => modifiedU x.1 x.2 + modifiedV x.1 x.2)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (omega * modifiedU p q + omega ^ 2 * modifiedV p q)) := by
  have hc : Continuous fun x : ℝ × ℝ =>
      ((2 * (principal (upperRadicand x.1 x.2)).re : ℝ) : ℂ) :=
    continuous_ofReal.comp
      (continuous_const.mul (continuous_re.comp continuous_principal_upperRadicand))
  have hlim : Tendsto (fun x : ℝ × ℝ => ((2 * (principal (upperRadicand x.1 x.2)).re : ℝ) : ℂ))
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 ((2 * (principal (upperRadicand p q)).re : ℝ) : ℂ)) :=
    (hc.tendsto (p, q)).mono_left nhdsWithin_le_nhds
  have hval : ((2 * (principal (upperRadicand p q)).re : ℝ) : ℂ) =
      omega * modifiedU p q + omega ^ 2 * modifiedV p q := by
    rw [principal_upperRadicand_re hΔ hq, modifiedU_of_eq_zero hΔ, modifiedV_of_eq_zero hΔ,
      omega_mul_ofReal_add]
    push_cast
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (modifiedU_add_modifiedV_of_neg hx).symm

/-- Approaching through negative discriminant, the second Cardano value tends
to the first Cardano value of the limit point. -/
theorem tendsto_omega_mul_modifiedU_add_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => omega * modifiedU x.1 x.2 + omega ^ 2 * modifiedV x.1 x.2)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedU p q + modifiedV p q)) := by
  have hc : Continuous fun x : ℝ × ℝ =>
      ((-(principal (upperRadicand x.1 x.2)).re -
        Real.sqrt 3 * (principal (upperRadicand x.1 x.2)).im : ℝ) : ℂ) :=
    continuous_ofReal.comp
      ((continuous_re.comp continuous_principal_upperRadicand).neg.sub
        (continuous_const.mul (continuous_im.comp continuous_principal_upperRadicand)))
  have hlim : Tendsto (fun x : ℝ × ℝ => ((-(principal (upperRadicand x.1 x.2)).re -
        Real.sqrt 3 * (principal (upperRadicand x.1 x.2)).im : ℝ) : ℂ))
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 ((-(principal (upperRadicand p q)).re -
        Real.sqrt 3 * (principal (upperRadicand p q)).im : ℝ) : ℂ)) :=
    (hc.tendsto (p, q)).mono_left nhdsWithin_le_nhds
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hreal : -(principal (upperRadicand p q)).re -
      Real.sqrt 3 * (principal (upperRadicand p q)).im =
        realCubicSurd (-q / 2) + realCubicSurd (-q / 2) := by
    rw [principal_upperRadicand_re hΔ hq, principal_upperRadicand_im hΔ hq]
    linear_combination (realCubicSurd (-q / 2) / 2) * h3
  have hval : ((-(principal (upperRadicand p q)).re -
      Real.sqrt 3 * (principal (upperRadicand p q)).im : ℝ) : ℂ) =
        modifiedU p q + modifiedV p q := by
    rw [hreal, modifiedU_of_eq_zero hΔ, modifiedV_of_eq_zero hΔ, ofReal_add]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (omega_mul_modifiedU_add_of_neg hx).symm

/-- At such a point the first and second Cardano values are different. -/
theorem modifiedU_add_modifiedV_ne_of_eq_zero {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    modifiedU p q + modifiedV p q ≠ omega * modifiedU p q + omega ^ 2 * modifiedV p q := by
  have hc : realCubicSurd (-q / 2) < 0 := realCubicSurd_lt_zero (by linarith)
  rw [modifiedU_of_eq_zero hΔ, modifiedV_of_eq_zero hΔ, omega_mul_ofReal_add]
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero] at hre
  linarith

/-- The first Cardano value is not continuous at such a point. -/
theorem not_continuousAt_modifiedU_add_modifiedV {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt (fun x : ℝ × ℝ => modifiedU x.1 x.2 + modifiedV x.1 x.2) (p, q) := by
  intro h
  have := neBot_nhdsWithin_discriminant_neg hΔ
  have h1 : Tendsto (fun x : ℝ × ℝ => modifiedU x.1 x.2 + modifiedV x.1 x.2)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedU p q + modifiedV p q)) := h.tendsto.mono_left nhdsWithin_le_nhds
  exact modifiedU_add_modifiedV_ne_of_eq_zero hΔ hq
    (tendsto_nhds_unique h1 (tendsto_modifiedU_add_modifiedV_of_neg hΔ hq))

/-- The second Cardano value is not continuous at such a point. -/
theorem not_continuousAt_omega_mul_modifiedU_add {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt
      (fun x : ℝ × ℝ => omega * modifiedU x.1 x.2 + omega ^ 2 * modifiedV x.1 x.2) (p, q) := by
  intro h
  have := neBot_nhdsWithin_discriminant_neg hΔ
  have h1 : Tendsto
      (fun x : ℝ × ℝ => omega * modifiedU x.1 x.2 + omega ^ 2 * modifiedV x.1 x.2)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (omega * modifiedU p q + omega ^ 2 * modifiedV p q)) :=
    h.tendsto.mono_left nhdsWithin_le_nhds
  exact modifiedU_add_modifiedV_ne_of_eq_zero hΔ hq
    (tendsto_nhds_unique (tendsto_omega_mul_modifiedU_add_of_neg hΔ hq) h1)

/-! ### Depressed cubics through the two functions -/

@[simp] theorem realDepressedP_one_zero (p : ℝ) : realDepressedP 1 0 p = p := by
  simp [realDepressedP]

@[simp] theorem realDepressedQ_one_zero (p q : ℝ) : realDepressedQ 1 0 p q = q := by
  simp [realDepressedQ]

@[simp] theorem cubicDiscriminant_one_zero (p q : ℝ) :
    cubicDiscriminant 1 0 p q = realDiscriminant p q := by
  simp [cubicDiscriminant]

theorem modifiedPrincipalCubicRoots_one_zero_x₀ (p q : ℝ) :
    (modifiedPrincipalCubicRoots 1 0 p q).x₀ = modifiedU p q + modifiedV p q := by
  simp [modifiedPrincipalCubicRoots_x₀_eq]

theorem modifiedPrincipalCubicRoots_one_zero_x₁ (p q : ℝ) :
    (modifiedPrincipalCubicRoots 1 0 p q).x₁ =
      omega * modifiedU p q + omega ^ 2 * modifiedV p q := by
  simp [modifiedPrincipalCubicRoots_x₁_eq]

/-! ### `modifiedPrincipalCubicRoots`: the first and second fields trade places -/

/-- Approaching through three distinct real roots, the first solution tends to
the second solution of the limit cubic. -/
theorem tendsto_modifiedPrincipalCubicRoots_x₀_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => (modifiedPrincipalCubicRoots 1 0 x.1 x.2).x₀)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedPrincipalCubicRoots 1 0 p q).x₁) := by
  simpa only [modifiedPrincipalCubicRoots_one_zero_x₀, modifiedPrincipalCubicRoots_one_zero_x₁]
    using tendsto_modifiedU_add_modifiedV_of_neg hΔ hq

/-- Approaching through three distinct real roots, the second solution tends
to the first solution of the limit cubic. -/
theorem tendsto_modifiedPrincipalCubicRoots_x₁_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => (modifiedPrincipalCubicRoots 1 0 x.1 x.2).x₁)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedPrincipalCubicRoots 1 0 p q).x₀) := by
  simpa only [modifiedPrincipalCubicRoots_one_zero_x₀, modifiedPrincipalCubicRoots_one_zero_x₁]
    using tendsto_omega_mul_modifiedU_add_of_neg hΔ hq

/-- The first and second solutions of the limit cubic are different. -/
theorem modifiedPrincipalCubicRoots_x₀_ne_x₁ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    (modifiedPrincipalCubicRoots 1 0 p q).x₀ ≠ (modifiedPrincipalCubicRoots 1 0 p q).x₁ := by
  simpa only [modifiedPrincipalCubicRoots_one_zero_x₀, modifiedPrincipalCubicRoots_one_zero_x₁]
    using modifiedU_add_modifiedV_ne_of_eq_zero hΔ hq

/-- The first solution is not continuous in the coefficients. -/
theorem not_continuousAt_modifiedPrincipalCubicRoots_x₀ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt (fun x : ℝ × ℝ => (modifiedPrincipalCubicRoots 1 0 x.1 x.2).x₀) (p, q) := by
  simpa only [modifiedPrincipalCubicRoots_one_zero_x₀]
    using not_continuousAt_modifiedU_add_modifiedV hΔ hq

/-- The second solution is not continuous in the coefficients. -/
theorem not_continuousAt_modifiedPrincipalCubicRoots_x₁ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt (fun x : ℝ × ℝ => (modifiedPrincipalCubicRoots 1 0 x.1 x.2).x₁) (p, q) := by
  simpa only [modifiedPrincipalCubicRoots_one_zero_x₁]
    using not_continuousAt_omega_mul_modifiedU_add hΔ hq

/-! ### `modifiedPrincipalCubicRootsReIm`: the first and third fields trade places -/

/-- Approaching through three distinct real roots, the first solution tends to
the third solution of the limit cubic. -/
theorem tendsto_modifiedPrincipalCubicRootsReIm_x₀_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => ((modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₀ : ℂ))
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedPrincipalCubicRootsReIm 1 0 p q).x₂) := by
  have hD : (0 : ℝ) ≤ cubicDiscriminant 1 0 p q := by
    rw [cubicDiscriminant_one_zero, hΔ]
  rw [modifiedPrincipalCubicRootsReIm_x₂_of_nonneg hD,
    ← modifiedPrincipalCubicRoots_x₁_eq_x₂ (by rw [cubicDiscriminant_one_zero, hΔ])]
  simpa only [modifiedPrincipalCubicRootsReIm_x₀_coe]
    using tendsto_modifiedPrincipalCubicRoots_x₀_of_neg hΔ hq

/-- Approaching through three distinct real roots, the third solution tends
to the first solution of the limit cubic. -/
theorem tendsto_modifiedPrincipalCubicRootsReIm_x₂_of_neg {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    Tendsto (fun x : ℝ × ℝ => (modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₂)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 ((modifiedPrincipalCubicRootsReIm 1 0 p q).x₀ : ℂ)) := by
  rw [modifiedPrincipalCubicRootsReIm_x₀_coe]
  refine (tendsto_modifiedPrincipalCubicRoots_x₁_of_neg hΔ hq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (modifiedPrincipalCubicRootsReIm_x₂_of_neg
    (by rw [cubicDiscriminant_one_zero]; exact hx)).symm

/-- The first and third solutions of the limit cubic are different. -/
theorem modifiedPrincipalCubicRootsReIm_x₀_ne_x₂ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ((modifiedPrincipalCubicRootsReIm 1 0 p q).x₀ : ℂ) ≠
      (modifiedPrincipalCubicRootsReIm 1 0 p q).x₂ := by
  have hD : (0 : ℝ) ≤ cubicDiscriminant 1 0 p q := by
    rw [cubicDiscriminant_one_zero, hΔ]
  rw [modifiedPrincipalCubicRootsReIm_x₀_coe, modifiedPrincipalCubicRootsReIm_x₂_of_nonneg hD,
    ← modifiedPrincipalCubicRoots_x₁_eq_x₂ (by rw [cubicDiscriminant_one_zero, hΔ])]
  exact modifiedPrincipalCubicRoots_x₀_ne_x₁ hΔ hq

/-- The first solution is not continuous in the coefficients. -/
theorem not_continuousAt_modifiedPrincipalCubicRootsReIm_x₀ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt (fun x : ℝ × ℝ => (modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₀) (p, q) := by
  intro h
  have := neBot_nhdsWithin_discriminant_neg hΔ
  have h1 : Tendsto (fun x : ℝ × ℝ => ((modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₀ : ℂ))
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 ((modifiedPrincipalCubicRootsReIm 1 0 p q).x₀ : ℂ)) :=
    ((continuous_ofReal.continuousAt.comp h).tendsto).mono_left nhdsWithin_le_nhds
  exact modifiedPrincipalCubicRootsReIm_x₀_ne_x₂ hΔ hq
    (tendsto_nhds_unique h1 (tendsto_modifiedPrincipalCubicRootsReIm_x₀_of_neg hΔ hq))

/-- The third solution is not continuous in the coefficients. -/
theorem not_continuousAt_modifiedPrincipalCubicRootsReIm_x₂ {p q : ℝ}
    (hΔ : realDiscriminant p q = 0) (hq : 0 < q) :
    ¬ContinuousAt (fun x : ℝ × ℝ => (modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₂) (p, q) := by
  intro h
  have := neBot_nhdsWithin_discriminant_neg hΔ
  have h1 : Tendsto (fun x : ℝ × ℝ => (modifiedPrincipalCubicRootsReIm 1 0 x.1 x.2).x₂)
      (𝓝[{x : ℝ × ℝ | realDiscriminant x.1 x.2 < 0}] (p, q))
      (𝓝 (modifiedPrincipalCubicRootsReIm 1 0 p q).x₂) :=
    h.tendsto.mono_left nhdsWithin_le_nhds
  exact modifiedPrincipalCubicRootsReIm_x₀_ne_x₂ hΔ hq
    (tendsto_nhds_unique (tendsto_modifiedPrincipalCubicRootsReIm_x₂_of_neg hΔ hq) h1)

end CubicEquation.CardanoReal
