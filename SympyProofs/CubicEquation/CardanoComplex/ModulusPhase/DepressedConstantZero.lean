module

public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Shortcuts
public import SympyProofs.CubicEquation.CardanoComplex.ModulusPhase.Realness

/-!
# The monic modulus-and-phase formula when the depressed constant vanishes

Write `p`, `q` for the depressed coefficients of `x^3 + a*x^2 + b*x + c`. When
`q = 0` the depressed cubic is `y^3 + p*y`, with solutions `0`, `I * sqrt p`
and `-(I * sqrt p)`. So `modulusPhaseMonicCubicRoots a b c` needs no cube root.

The position of the solution `0` depends on the argument of `p`:

* if `-π/3 < arg p ≤ π/3`, the order is `0`, `I * sqrt p`, `-(I * sqrt p)`;
* if `π/3 < arg p`, the order is `-(I * sqrt p)`, `I * sqrt p`, `0`;
* if `arg p ≤ -π/3`, the order is `I * sqrt p`, `0`, `-(I * sqrt p)`.

For real coefficients only the first two cases occur, by the sign of `p`.
-/

@[expose] public section

noncomputable section

namespace CubicEquation.CardanoComplex

open RealCubeRoot
open CardanoReal
open Complex
open scoped ComplexConjugate

/-! ### The first radical -/

/-- Polar form of the principal square root. -/
theorem sqrt_eq_polar (z : ℂ) :
    Complex.sqrt z = (Real.sqrt ‖z‖ : ℂ) *
      ((Real.cos (arg z / 2) : ℂ) + (Real.sin (arg z / 2) : ℂ) * I) := by
  have h := Complex.cpow_ofReal z (2⁻¹ : ℝ)
  rw [show ((2⁻¹ : ℝ) : ℂ) = (2⁻¹ : ℂ) by simp] at h
  rw [Complex.sqrt, h, Real.sqrt_eq_rpow, one_div, div_eq_mul_inv]

/-- The first radical for `q = 0`, in polar form. The angle `ψ` is `arg p / 2`
moved by a multiple of `π / 3` into the range of a principal cube root of a
principal square root. -/
private theorem firstRadical_zero_polar {p : ℂ} {ψ : ℝ} (h1 : -(Real.pi / 6) < ψ)
    (h2 : ψ ≤ Real.pi / 6) (hc : Real.cos (6 * ψ) = Real.cos (3 * arg p))
    (hs : Real.sin (6 * ψ) = Real.sin (3 * arg p)) :
    modifiedPrincipal (radicandPlus p 0) =
      (Real.sqrt (‖p‖ / 3) : ℂ) * ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * I) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [radicandPlus, discriminant]
  have hpi := Real.pi_pos
  have hnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hx : 0 < Real.sqrt (‖p‖ / 3) := Real.sqrt_pos.mpr (by positivity)
  have hx2 : (Real.sqrt (‖p‖ / 3) : ℂ) ^ 2 = (‖p‖ : ℂ) / 3 := by
    have h := Real.sq_sqrt (show 0 ≤ ‖p‖ / 3 by positivity)
    exact_mod_cast h
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  generalize Real.sqrt (‖p‖ / 3) = x at hx hx2 ⊢
  set t : ℂ := (x : ℂ) * (Complex.cos ψ + Complex.sin ψ * I) with ht
  have ht0 : t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hx.ne')
      (by rw [← Complex.exp_mul_I]; exact Complex.exp_ne_zero _)
  have harg : arg t = ψ := arg_mul_cos_add_sin_mul_I hx ⟨by linarith, by linarith⟩
  have ht3 : t ^ 3 = ((x ^ 3 : ℝ) : ℂ) *
      (Complex.cos ((3 * ψ : ℝ) : ℂ) + Complex.sin ((3 * ψ : ℝ) : ℂ) * I) := by
    rw [ht, mul_pow, Complex.cos_add_sin_mul_I_pow]
    push_cast
    rfl
  have harg3 : arg (t ^ 3) = 3 * ψ := by
    rw [ht3]
    exact arg_mul_cos_add_sin_mul_I (pow_pos hx 3) ⟨by linarith, by linarith⟩
  have hsqrt : Complex.sqrt ((t ^ 3) ^ 2) = t ^ 3 := by
    rw [Complex.sqrt]
    exact Complex.pow_cpow_ofNat_inv (by rw [harg3]; linarith) (by rw [harg3]; linarith)
  have hcube : principal (t ^ 3) = t := by
    rw [principal]
    exact Complex.pow_cpow_ofNat_inv (by rw [harg]; linarith) (by rw [harg]; linarith)
  have hD : discriminant p 0 = (t ^ 3) ^ 2 := by
    have hp3 : p ^ 3 = (‖p‖ : ℂ) ^ 3 *
        (Complex.cos (3 * (arg p : ℂ)) + Complex.sin (3 * (arg p : ℂ)) * I) := by
      conv_lhs => rw [← Complex.norm_mul_cos_add_sin_mul_I p]
      rw [mul_pow, Complex.cos_add_sin_mul_I_pow]
      norm_num
    have ht6 : (t ^ 3) ^ 2 = (x : ℂ) ^ 6 *
        (Complex.cos (6 * (ψ : ℂ)) + Complex.sin (6 * (ψ : ℂ)) * I) := by
      rw [← pow_mul, ht, mul_pow, Complex.cos_add_sin_mul_I_pow]
      norm_num
    have hcc : Complex.cos (6 * (ψ : ℂ)) = Complex.cos (3 * (arg p : ℂ)) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hc
    have hsc : Complex.sin (6 * (ψ : ℂ)) = Complex.sin (3 * (arg p : ℂ)) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hs
    rw [discriminant, ht6, hp3, hcc, hsc]
    linear_combination
      (-(Complex.cos (3 * (arg p : ℂ)) + Complex.sin (3 * (arg p : ℂ)) * I) *
        ((x : ℂ) ^ 4 + (x : ℂ) ^ 2 * (‖p‖ : ℂ) / 3 + (‖p‖ : ℂ) ^ 2 / 9)) * hx2
  have hA : radicandPlus p 0 = t ^ 3 := by
    rw [radicandPlus, hD, hsqrt, neg_zero, zero_div, zero_add]
  have hslit : t ^ 3 ∈ slitPlane :=
    mem_slitPlane_iff_arg.mpr
      ⟨(by rw [harg3]; linarith : arg (t ^ 3) < Real.pi).ne, pow_ne_zero 3 ht0⟩
  rw [hA, modifiedPrincipal_eq_principal hslit, hcube]

private theorem sqrt_div_three (r : ℝ) (hr : 0 ≤ r) :
    Real.sqrt (r / 3) = Real.sqrt r * Real.sqrt 3 / 3 := by
  rw [show r / 3 = (Real.sqrt r * Real.sqrt 3 / 3) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt (by norm_num)]; ring,
    Real.sqrt_sq (by positivity)]

/-- For `q = 0` and `-π/3 < arg p ≤ π/3`, the first radical is `sqrt p / sqrt 3`. -/
theorem firstRadical_zero_of_arg_mem {p : ℂ} (h1 : -(Real.pi / 3) < arg p)
    (h2 : arg p ≤ Real.pi / 3) :
    modifiedPrincipal (radicandPlus p 0) = (Real.sqrt 3 : ℂ) / 3 * Complex.sqrt p := by
  rw [firstRadical_zero_polar (ψ := arg p / 2) (by linarith) (by linarith)
    (by congr 1; ring) (by congr 1; ring), sqrt_eq_polar p, sqrt_div_three _ (norm_nonneg p)]
  push_cast
  ring

/-- For `q = 0` and `π/3 < arg p`, the first radical is `sqrt p / sqrt 3` turned by `-π/3`. -/
theorem firstRadical_zero_of_lt_arg {p : ℂ} (h : Real.pi / 3 < arg p) :
    modifiedPrincipal (radicandPlus p 0) =
      -omega * ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt p) := by
  have hle := Complex.arg_le_pi p
  rw [firstRadical_zero_polar (ψ := arg p / 2 - Real.pi / 3) (by linarith) (by linarith)
    (by rw [show 6 * (arg p / 2 - Real.pi / 3) = 3 * arg p - 2 * Real.pi by ring,
      Real.cos_sub_two_pi])
    (by rw [show 6 * (arg p / 2 - Real.pi / 3) = 3 * arg p - 2 * Real.pi by ring,
      Real.sin_sub_two_pi]),
    sqrt_eq_polar p, sqrt_div_three _ (norm_nonneg p), Real.cos_sub, Real.sin_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three, omega]
  push_cast
  linear_combination ((Real.sqrt ‖p‖ : ℂ) * (Real.sqrt 3 : ℂ) ^ 2 *
    Complex.sin ((arg p : ℂ) / 2) / 6) * Complex.I_sq

/-- For `q = 0` and `arg p ≤ -π/3`, the first radical is `sqrt p / sqrt 3` turned by `π/3`. -/
theorem firstRadical_zero_of_arg_le {p : ℂ} (h : arg p ≤ -(Real.pi / 3)) :
    modifiedPrincipal (radicandPlus p 0) =
      -omega ^ 2 * ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt p) := by
  have hlt := Complex.neg_pi_lt_arg p
  rw [firstRadical_zero_polar (ψ := arg p / 2 + Real.pi / 3) (by linarith) (by linarith)
    (by rw [show 6 * (arg p / 2 + Real.pi / 3) = 3 * arg p + 2 * Real.pi by ring,
      Real.cos_add_two_pi])
    (by rw [show 6 * (arg p / 2 + Real.pi / 3) = 3 * arg p + 2 * Real.pi by ring,
      Real.sin_add_two_pi]),
    sqrt_eq_polar p, sqrt_div_three _ (norm_nonneg p), Real.cos_add, Real.sin_add,
    Real.cos_pi_div_three, Real.sin_pi_div_three, omega_sq, omega]
  push_cast
  linear_combination (-((Real.sqrt ‖p‖ : ℂ) * (Real.sqrt 3 : ℂ) ^ 2 *
    Complex.sin ((arg p : ℂ) / 2) / 6)) * Complex.I_sq

/-! ### The second radical -/

private theorem sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem scaled_sqrt_sq (p : ℂ) :
    ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt p) ^ 2 = p / 3 := by
  linear_combination (Complex.sqrt p ^ 2 / 9) * sqrt_three_sq + (1 / 3 : ℂ) * sqrt_sq p

private theorem two_omega_add_one_mul (p : ℂ) :
    (2 * omega + 1) * ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt p) = I * Complex.sqrt p := by
  rw [omega]
  linear_combination (I * Complex.sqrt p / 3) * sqrt_three_sq

/-- For `q = 0` and `-π/3 < arg p ≤ π/3`, the second radical is minus the first. -/
theorem modulusPhaseV_zero_of_arg_mem {p : ℂ} (h1 : -(Real.pi / 3) < arg p)
    (h2 : arg p ≤ Real.pi / 3) :
    modulusPhaseV p 0 = -modifiedPrincipal (radicandPlus p 0) := by
  rcases eq_or_ne p 0 with rfl | hp
  · have h0 : radicandPlus 0 0 = 0 := by simp [radicandPlus, discriminant]
    rw [modulusPhaseV_of_eq_zero h0, h0]
    simp
  have hA := radicandPlus_ne_zero_of_ne_zero hp 0
  have hu : modifiedPrincipal (radicandPlus p 0) ≠ 0 := fun h =>
    hA (modifiedPrincipal_eq_zero_iff.mp h)
  rw [modulusPhaseV_of_ne_zero hA, div_eq_iff (mul_ne_zero three_ne_zero hu),
    firstRadical_zero_of_arg_mem h1 h2]
  linear_combination 3 * scaled_sqrt_sq p

/-- For `q = 0` and `π/3 < arg p`, the second radical is `-ω` times the first. -/
theorem modulusPhaseV_zero_of_lt_arg {p : ℂ} (h : Real.pi / 3 < arg p) :
    modulusPhaseV p 0 = -omega * modifiedPrincipal (radicandPlus p 0) := by
  have hp : p ≠ 0 := by
    rintro rfl
    rw [arg_zero] at h
    linarith [Real.pi_pos]
  have hA := radicandPlus_ne_zero_of_ne_zero hp 0
  have hu : modifiedPrincipal (radicandPlus p 0) ≠ 0 := fun h =>
    hA (modifiedPrincipal_eq_zero_iff.mp h)
  rw [modulusPhaseV_of_ne_zero hA, div_eq_iff (mul_ne_zero three_ne_zero hu),
    firstRadical_zero_of_lt_arg h]
  linear_combination 3 * omega ^ 3 * scaled_sqrt_sq p + p * omega_cube

/-- For `q = 0` and `arg p ≤ -π/3`, the second radical is `-ω^2` times the first. -/
theorem modulusPhaseV_zero_of_arg_le {p : ℂ} (h : arg p ≤ -(Real.pi / 3)) :
    modulusPhaseV p 0 = -omega ^ 2 * modifiedPrincipal (radicandPlus p 0) := by
  have hp : p ≠ 0 := by
    rintro rfl
    rw [arg_zero] at h
    linarith [Real.pi_pos]
  have hA := radicandPlus_ne_zero_of_ne_zero hp 0
  have hu : modifiedPrincipal (radicandPlus p 0) ≠ 0 := fun h =>
    hA (modifiedPrincipal_eq_zero_iff.mp h)
  rw [modulusPhaseV_of_ne_zero hA, div_eq_iff (mul_ne_zero three_ne_zero hu),
    firstRadical_zero_of_arg_le h]
  linear_combination 3 * omega ^ 6 * scaled_sqrt_sq p + p * (omega ^ 3 + 1) * omega_cube

/-! ### The three solutions -/

/-- When `q = 0` and `-π/3 < arg p ≤ π/3`, the solutions are `0`, `I * sqrt p`
and `-(I * sqrt p)`, in this order, shifted by `-a/3`. -/
theorem modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_arg_mem {a b c : ℂ}
    (hq : complexMonicDepressedQ a b c = 0)
    (h1 : -(Real.pi / 3) < arg (complexMonicDepressedP a b))
    (h2 : arg (complexMonicDepressedP a b) ≤ Real.pi / 3) :
    modulusPhaseMonicCubicRoots a b c =
      { x₀ := -(a / 3)
        x₁ := I * Complex.sqrt (complexMonicDepressedP a b) - a / 3
        x₂ := -(I * Complex.sqrt (complexMonicDepressedP a b)) - a / 3 } := by
  have hI := two_omega_add_one_mul (complexMonicDepressedP a b)
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, hq, modulusPhaseV_zero_of_arg_mem h1 h2,
      modifiedConjugateCorrectedU]
    ring
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, hq, modulusPhaseV_zero_of_arg_mem h1 h2,
      modifiedConjugateCorrectedU, firstRadical_zero_of_arg_mem h1 h2]
    linear_combination hI -
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, hq, modulusPhaseV_zero_of_arg_mem h1 h2,
      modifiedConjugateCorrectedU, firstRadical_zero_of_arg_mem h1 h2]
    linear_combination
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic - hI

/-- When `q = 0` and `π/3 < arg p`, the solutions are `-(I * sqrt p)`,
`I * sqrt p` and `0`, in this order, shifted by `-a/3`. -/
theorem modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_lt_arg {a b c : ℂ}
    (hq : complexMonicDepressedQ a b c = 0)
    (h : Real.pi / 3 < arg (complexMonicDepressedP a b)) :
    modulusPhaseMonicCubicRoots a b c =
      { x₀ := -(I * Complex.sqrt (complexMonicDepressedP a b)) - a / 3
        x₁ := I * Complex.sqrt (complexMonicDepressedP a b) - a / 3
        x₂ := -(a / 3) } := by
  have hI := two_omega_add_one_mul (complexMonicDepressedP a b)
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, hq, modulusPhaseV_zero_of_lt_arg h,
      modifiedConjugateCorrectedU, firstRadical_zero_of_lt_arg h]
    linear_combination
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic - hI
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, hq, modulusPhaseV_zero_of_lt_arg h,
      modifiedConjugateCorrectedU, firstRadical_zero_of_lt_arg h]
    linear_combination hI + (omega * (omega - 1) - 1) *
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, hq, modulusPhaseV_zero_of_lt_arg h,
      modifiedConjugateCorrectedU]
    ring

/-- When `q = 0` and `arg p ≤ -π/3`, the solutions are `I * sqrt p`, `0` and
`-(I * sqrt p)`, in this order, shifted by `-a/3`. -/
theorem modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_arg_le {a b c : ℂ}
    (hq : complexMonicDepressedQ a b c = 0)
    (h : arg (complexMonicDepressedP a b) ≤ -(Real.pi / 3)) :
    modulusPhaseMonicCubicRoots a b c =
      { x₀ := I * Complex.sqrt (complexMonicDepressedP a b) - a / 3
        x₁ := -(a / 3)
        x₂ := -(I * Complex.sqrt (complexMonicDepressedP a b)) - a / 3 } := by
  have hI := two_omega_add_one_mul (complexMonicDepressedP a b)
  refine CardanoRoots.ext ?_ ?_ ?_
  · rw [modulusPhaseMonicCubicRoots_x₀_eq, hq, modulusPhaseV_zero_of_arg_le h,
      modifiedConjugateCorrectedU, firstRadical_zero_of_arg_le h]
    linear_combination hI + (omega * (omega - 1) - 1) *
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic
  · rw [modulusPhaseMonicCubicRoots_x₁_eq, hq, modulusPhaseV_zero_of_arg_le h,
      modifiedConjugateCorrectedU, firstRadical_zero_of_arg_le h]
    linear_combination omega ^ 3 * (omega - 1) *
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic
  · rw [modulusPhaseMonicCubicRoots_x₂_eq, hq, modulusPhaseV_zero_of_arg_le h,
      modifiedConjugateCorrectedU, firstRadical_zero_of_arg_le h]
    linear_combination (omega * (omega - 1) ^ 2 + 1) *
      ((Real.sqrt 3 : ℂ) / 3 * Complex.sqrt (complexMonicDepressedP a b)) * omega_quadratic - hI

/-! ### Real coefficients -/

/-- For real coefficients with `q = 0` and `0 ≤ p`, the solutions are the real
one `-a/3` and the conjugate pair `-a/3 ± I * sqrt p`. -/
theorem modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_nonneg {a b c : ℝ}
    (hq : monicDepressedQ a b c = 0) (hp : 0 ≤ monicDepressedP a b) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c =
      { x₀ := ((-(a / 3) : ℝ) : ℂ)
        x₁ := ((-(a / 3) : ℝ) : ℂ) + (Real.sqrt (monicDepressedP a b) : ℂ) * I
        x₂ := ((-(a / 3) : ℝ) : ℂ) - (Real.sqrt (monicDepressedP a b) : ℂ) * I } := by
  have hq' : complexMonicDepressedQ (a : ℂ) b c = 0 := by
    rw [complexMonicDepressedQ_ofReal, hq, ofReal_zero]
  have harg : arg (complexMonicDepressedP (a : ℂ) b) = 0 := by
    rw [complexMonicDepressedP_ofReal, arg_ofReal_of_nonneg hp]
  have hsqrt : Complex.sqrt (complexMonicDepressedP (a : ℂ) b) =
      (Real.sqrt (monicDepressedP a b) : ℂ) := by
    rw [complexMonicDepressedP_ofReal, sqrt_ofReal,
      Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hp)]
    simp
  rw [modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_arg_mem hq'
    (by rw [harg]; linarith [Real.pi_pos]) (by rw [harg]; linarith [Real.pi_pos]), hsqrt]
  refine CardanoRoots.ext ?_ ?_ ?_ <;> push_cast <;> ring

/-- For real coefficients with `q = 0` and `p < 0`, the three solutions are
real: `sqrt (-p) - a/3`, `-sqrt (-p) - a/3` and `-a/3`, in this order. -/
theorem modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_neg {a b c : ℝ}
    (hq : monicDepressedQ a b c = 0) (hp : monicDepressedP a b < 0) :
    modulusPhaseMonicCubicRoots (a : ℂ) b c =
      { x₀ := ((Real.sqrt (-monicDepressedP a b) - a / 3 : ℝ) : ℂ)
        x₁ := ((-Real.sqrt (-monicDepressedP a b) - a / 3 : ℝ) : ℂ)
        x₂ := ((-(a / 3) : ℝ) : ℂ) } := by
  have hq' : complexMonicDepressedQ (a : ℂ) b c = 0 := by
    rw [complexMonicDepressedQ_ofReal, hq, ofReal_zero]
  have harg : arg (complexMonicDepressedP (a : ℂ) b) = Real.pi := by
    rw [complexMonicDepressedP_ofReal, arg_ofReal_of_neg hp]
  have hsqrt : Complex.sqrt (complexMonicDepressedP (a : ℂ) b) =
      (Real.sqrt (-monicDepressedP a b) : ℂ) * I := by
    rw [complexMonicDepressedP_ofReal, sqrt_ofReal, Real.sqrt_eq_zero_of_nonpos hp.le]
    simp
  rw [modulusPhaseMonicCubicRoots_of_depressedQ_eq_zero_of_lt_arg hq'
    (by rw [harg]; linarith [Real.pi_pos]), hsqrt]
  refine CardanoRoots.ext ?_ ?_ ?_
  · push_cast
    linear_combination (-(Real.sqrt (-monicDepressedP a b) : ℂ)) * Complex.I_sq
  · push_cast
    linear_combination (Real.sqrt (-monicDepressedP a b) : ℂ) * Complex.I_sq
  · push_cast
    ring

end CubicEquation.CardanoComplex
