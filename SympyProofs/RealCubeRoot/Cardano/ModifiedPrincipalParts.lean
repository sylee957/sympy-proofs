module

public import SympyProofs.RealCubeRoot.Cardano.ModifiedPrincipal

/-!
# Cardano's modified-principal formula with real and imaginary parts

For real depressed coefficients `p,q`, form the sum `W` of the two principal
cube roots. Then `r = W.re - sqrt(3) * W.im` is a real root. Factoring out
`x - r` gives the other two roots as `(-r ± sqrt(-3*r^2 - 4*p)) / 2`.

`cardano_formula_modifiedPrincipal_re_im` displays the complete formula with
`let` bindings. It uses no modified-root function, conjugation, roots of unity,
conditionals, or division by radicals. Only the leading coefficient must be
nonzero; repeated and triple roots are included. Both square roots are complex
principal square roots, so the other two solutions may be nonreal.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot.Cardano

open Complex
open scoped ComplexConjugate

/-- Conjugation fixes the two Cardano radicands individually or exchanges them. -/
private theorem radicand_pair_conj_sum (F : ℂ → ℂ) (p q : ℝ) :
    F (conj (radicandPlus (p : ℂ) q)) + F (conj (radicandMinus (p : ℂ) q)) =
      F (radicandPlus (p : ℂ) q) + F (radicandMinus (p : ℂ) q) := by
  let s := Complex.sqrt (discriminant (p : ℂ) q)
  have hs : conj s ^ 2 = s ^ 2 := by
    rw [← map_pow]
    change conj (Complex.sqrt (discriminant (p : ℂ) q) ^ 2) =
      Complex.sqrt (discriminant (p : ℂ) q) ^ 2
    rw [sqrt_sq, discriminant_ofReal, conj_ofReal]
  change F (conj (-((q : ℂ)) / 2 + s)) + F (conj (-((q : ℂ)) / 2 - s)) = _
  rcases eq_or_eq_neg_of_sq_eq_sq (conj s) s hs with hs | hs
  · simp only [map_add, map_sub, map_div₀, map_neg, conj_ofReal, hs,
      show conj (2 : ℂ) = 2 from conj_ofReal 2]
    rfl
  · simp only [map_add, map_sub, map_div₀, map_neg, conj_ofReal, hs,
      show conj (2 : ℂ) = 2 from conj_ofReal 2, sub_neg_eq_add]
    change F (-((q : ℂ)) / 2 - s) + F (-((q : ℂ)) / 2 + s) = _
    exact add_comm _ _

/-- A real root obtained directly from the real and imaginary parts of the
sum of the principal cube roots. -/
def principalRealRoot (p q : ℝ) : ℝ :=
  let W := principal (radicandPlus (p : ℂ) q) + principal (radicandMinus (p : ℂ) q)
  W.re - Real.sqrt 3 * W.im

/-- The simplified expression equals the first modified-principal Cardano root. -/
theorem principalRealRoot_coe (p q : ℝ) :
    (principalRealRoot p q : ℂ) =
      modifiedPrincipal (radicandPlus (p : ℂ) q) +
        modifiedPrincipal (radicandMinus (p : ℂ) q) := by
  simpa only [principalRealRoot] using
    (modifiedPrincipal_add_eq_re_im (radicand_pair_conj_sum principal p q)).symm

/-- The simplified real expression solves the depressed cubic for every real `p,q`. -/
theorem principalRealRoot_spec (p q : ℝ) :
    principalRealRoot p q ^ 3 + p * principalRealRoot p q + q = 0 := by
  have h := (mem_modifiedPrincipal_pairedRoots_iff p q _).mp
    (show modifiedPrincipal (radicandPlus (p : ℂ) q) +
      modifiedPrincipal (radicandMinus (p : ℂ) q) ∈
      pairedRoots (modifiedPrincipal (radicandPlus (p : ℂ) q))
        (modifiedPrincipal (radicandMinus (p : ℂ) q)) from by simp [pairedRoots])
  rw [← principalRealRoot_coe] at h
  exact_mod_cast h

/-- Given any root, the remaining quadratic gives an exact factorization.
No distinctness or nonzero-root assumption is needed. -/
theorem depressed_factorization_of_root {p q r : ℂ}
    (hr : r ^ 3 + p * r + q = 0) (x : ℂ) :
    (x - r) * (x - (-r + Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2) *
      (x - (-r - Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2) =
        x ^ 3 + p * x + q := by
  have hs := sqrt_sq (-3 * r ^ 2 - 4 * p)
  linear_combination -(x - r) / 4 * hs - hr

/-- A known root and the two quadratic expressions give precisely all solutions. -/
theorem depressed_roots_iff_of_root {p q r : ℂ}
    (hr : r ^ 3 + p * r + q = 0) (x : ℂ) :
    x ^ 3 + p * x + q = 0 ↔ x = r ∨
      x = (-r + Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2 ∨
      x = (-r - Complex.sqrt (-3 * r ^ 2 - 4 * p)) / 2 := by
  rw [← depressed_factorization_of_root hr x]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

/-- Shift a real depressed root and its quadratic companions back to the original cubic. -/
theorem cubic_roots_iff_of_real_depressed_root {a : ℝ} (ha : a ≠ 0)
    (b c d r : ℝ)
    (hr : r ^ 3 + (c / a - (b / a) ^ 2 / 3) * r +
      (2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a) = 0) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let t := Complex.sqrt (-3 * (r : ℂ) ^ 2 - 4 * (p : ℂ))
    let shift : ℝ := (b / a) / 3
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = (r : ℂ) - shift ∨
      x = (-(r : ℂ) + t) / 2 - shift ∨
      x = (-(r : ℂ) - t) / 2 - shift := by
  dsimp only
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  let shift : ℝ := (b / a) / 3
  have hr' : (r : ℂ) ^ 3 + (p : ℂ) * r + q = 0 := by exact_mod_cast hr
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hscale : (a : ℂ) *
      (x ^ 3 + ((b : ℂ) / a) * x ^ 2 + ((c : ℂ) / a) * x + (d : ℂ) / a) =
      (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d := by
    field_simp
  have hshift : (shift : ℂ) = ((b : ℂ) / a) / 3 := by
    simp [shift]
  have hnorm : (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      (x + (shift : ℂ)) ^ 3 + (p : ℂ) * (x + (shift : ℂ)) + q = 0 := by
    rw [show (p : ℂ) = depressedP (a : ℂ) b c from (depressedP_ofReal a b c).symm,
      show (q : ℂ) = depressedQ (a : ℂ) b c d from (depressedQ_ofReal a b c d).symm,
      hshift, depressed_shift, ← hscale, mul_eq_zero]
    simp [ha']
  rw [hnorm, depressed_roots_iff_of_root hr']
  simp only [eq_sub_iff_add_eq]
  rfl

/-- The uniform Cardano formula using principal cube roots and real/imaginary
parts. All three solutions are explicit, with no conditional or radical in a
denominator, for every real cubic with `a ≠ 0`. -/
theorem cardano_formula_modifiedPrincipal_re_im {a : ℝ} (ha : a ≠ 0)
    (b c d : ℝ) (x : ℂ) :
    let p : ℝ := c / a - (b / a) ^ 2 / 3
    let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
    let Δ : ℝ := q ^ 2 / 4 + p ^ 3 / 27
    let s := Complex.sqrt (Δ : ℂ)
    let W := principal (-(q : ℂ) / 2 + s) + principal (-(q : ℂ) / 2 - s)
    let r : ℝ := W.re - Real.sqrt 3 * W.im
    let t := Complex.sqrt (-3 * (r : ℂ) ^ 2 - 4 * (p : ℂ))
    let shift : ℝ := (b / a) / 3
    let x₀ := (r : ℂ) - shift
    let x₁ := (-(r : ℂ) + t) / 2 - shift
    let x₂ := (-(r : ℂ) - t) / 2 - shift
    (a : ℂ) * x ^ 3 + (b : ℂ) * x ^ 2 + (c : ℂ) * x + d = 0 ↔
      x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  let p : ℝ := c / a - (b / a) ^ 2 / 3
  let q : ℝ := 2 * (b / a) ^ 3 / 27 - (b / a) * (c / a) / 3 + d / a
  simpa only [principalRealRoot, radicandPlus, radicandMinus,
    discriminant_ofReal, realDiscriminant, p, q] using
    cubic_roots_iff_of_real_depressed_root ha b c d (principalRealRoot p q)
      (principalRealRoot_spec p q) x

end RealCubeRoot.Cardano
