module

public import SympyProofs.RealCubeRoot.Cardano.ConjugateCorrected

/-!
# A nonreal first root for real coefficients

The conjugate-corrected formula can return a nonreal first root even when all
coefficients are real. The theorem displays that formula with intermediate
quantities; its proof uses `x^3 - 6*x + 9 = 0` as a witness.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate ComplexOrder

/-- There are real coefficients with nonzero leading coefficient for which the
first conjugate-corrected Cardano root is not real. -/
theorem exists_conjugateCorrected_first_not_real :
    ∃ a b c d : ℝ, a ≠ 0 ∧
      let p : ℝ := c / a - (b / a) ^ 2 / 3
      let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
      let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
      let A := -(q : ℂ) / 2 + Complex.sqrt (Δ : ℂ)
      let B := -(q : ℂ) / 2 - Complex.sqrt (Δ : ℂ)
      let C := -(p : ℂ) / 3
      let E : ℂ → ℂ := fun r =>
        (principal (-1 + r * I) - conj (principal (-1 - r * I))) /
          (I * (Real.sqrt 3 : ℂ))
      let u := principal A
      let w := principal B
      let r := u * conj u
      let e := E r
      let v := (C * conj u + e * w) / (r + e)
      let shift : ℝ := (b / a) / 3
      let x₀ := u + v - (shift : ℂ)
      x₀.im ≠ 0 := by
  refine ⟨1, 0, -6, 9, by norm_num, ?_⟩
  have hsqrt : Complex.sqrt (discriminant (-6) 9) = (7 : ℂ) / 2 := by
    have hd : discriminant (-6) 9 = (49 : ℂ) / 4 := by norm_num [discriminant]
    rw [hd, Complex.sqrt_of_nonneg
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 49 / 4)]
    norm_num [Real.sqrt_div]
  have hA : radicandPlus (-6) 9 = -1 := by
    norm_num [radicandPlus, hsqrt]
  have hu : u (-6) 9 = (1 + (Real.sqrt 3 : ℂ) * I) / 2 := by
    rw [u, hA]
    simpa using principal_ofReal_of_neg (by norm_num : (-1 : ℝ) < 0)
  have hu0 : u (-6) 9 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hu] at this
  have hv : conjugateCorrectedV (-6) 9 = 1 - (Real.sqrt 3 : ℂ) * I := by
    apply mul_left_cancel₀ hu0
    rw [conjugateCorrected_uv, hu]
    have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    calc
      -(-6 : ℂ) / 3 = 2 := by norm_num
      _ = (1 - (Real.sqrt 3 : ℂ) ^ 2 * I ^ 2) / 2 := by rw [hs, I_sq]; norm_num
      _ = ((1 + (Real.sqrt 3 : ℂ) * I) / 2) * (1 - (Real.sqrt 3 : ℂ) * I) := by ring
  have hfirst : u (-6) 9 + conjugateCorrectedV (-6) 9 =
      3 / 2 - (Real.sqrt 3 : ℂ) * I / 2 := by
    rw [hu, hv]
    ring
  have hnot : (u (-6) 9 + conjugateCorrectedV (-6) 9).im ≠ 0 := by
    rw [hfirst]
    simp
  convert hnot using 1
  norm_num [u, conjugateCorrectedV, conjugatePairedRoot, conjugateZeroDetector,
    radicandPlus, radicandMinus, discriminant]

end RealCubeRoot.Cardano
