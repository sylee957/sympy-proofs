module

public import SympyProofs.Geometry.Evolute
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The evolute of an ellipse

The general notions are in `SympyProofs.Geometry.Evolute`. The evolute of a set
of points is the set of limits of centres of circles through three of its
points, `IsLimitCircumcenter`, and `centerOfCurvature γ t` is the formula of
differential geometry for a parametrized curve.

`ellipse_evolute` states that a point `X` is on the evolute of the ellipse with
centre `C` and radii `a`, `b`, the set `ellipse C a b` of `PointConicDistance`,
exactly when

`|a (X.x - C.x)|^(2/3) + |b (X.y - C.y)|^(2/3) - |a² - b²|^(2/3) = 0`.

The radii need only be nonzero. When `a² = b²` the curve is a circle, the
evolute is its centre, and the equation says the same.

The powers are real powers of nonnegative numbers. Without the absolute values
the bases can be negative, and the statement is not about that expression.

The proof has two halves. The ellipse is traced by
`ellipsePoint C a b t = C + (a cos t, b sin t)`, and the formula gives its
centre of curvature `C + ((a² - b²)/a · cos³ t, (b² - a²)/b · sin³ t)`.
Independently, the centre of the circle through three points of the ellipse is
a polynomial in their coordinates, `ellipseCircumcenter`, so its limit as the
points tend to `P` is its value at three equal points.
`ellipse_isLimitCircumcenter_ellipsePoint` shows the two agree, and
`mem_evolute_ellipse_iff` traces the evolute by the formula.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open scoped InnerProductSpace

/-! ### The ellipse -/

/-- The trigonometric parametrization of the ellipse with centre `C` and radii `a`, `b`. -/
def ellipsePoint (C : Point2D) (a b t : ℝ) : Point2D := C + !₂[a * Real.cos t, b * Real.sin t]

private theorem exists_cos_sin (p q : ℝ) (h : p ^ 2 + q ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = p ∧ Real.sin t = q := by
  have hnorm : ‖(⟨p, q⟩ : ℂ)‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_mk]
    linear_combination h
  obtain ⟨t, ht⟩ := (Complex.norm_eq_one_iff _).mp hnorm
  refine ⟨t, ?_, ?_⟩
  · simpa [Complex.exp_ofReal_mul_I_re] using congrArg Complex.re ht
  · simpa [Complex.exp_ofReal_mul_I_im] using congrArg Complex.im ht

/-- The parametrization traces the whole implicit ellipse. -/
theorem range_ellipsePoint (C : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set.range (ellipsePoint C a b) = ellipse C a b := by
  ext Y
  simp only [Set.mem_range, ellipse, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp only [ellipsePoint, PiLp.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination a ^ 2 * b ^ 2 * Real.cos_sq_add_sin_sq t
  · intro hY
    obtain ⟨t, hcos, hsin⟩ := exists_cos_sin ((Y 0 - C 0) / a) ((Y 1 - C 1) / b) (by
      field_simp
      linear_combination hY)
    refine ⟨t, ?_⟩
    rw [point_eq_iff]
    simp only [ellipsePoint, PiLp.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hcos, hsin]
    constructor <;> field_simp <;> ring

private theorem hasDerivAt_point {f : ℝ → Point2D} {f' : Point2D} {t : ℝ}
    (h0 : HasDerivAt (fun s => f s 0) (f' 0) t) (h1 : HasDerivAt (fun s => f s 1) (f' 1) t) :
    HasDerivAt f f' t := by
  have h : HasDerivAt (fun s => (WithLp.ofLp (f s) : Fin 2 → ℝ)) (WithLp.ofLp f') t :=
    hasDerivAt_pi.mpr fun i => by
      fin_cases i
      · exact h0
      · exact h1
  exact (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 2 => ℝ).symm.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_ellipsePoint (C : Point2D) (a b t : ℝ) :
    HasDerivAt (ellipsePoint C a b) !₂[-a * Real.sin t, b * Real.cos t] t := by
  apply hasDerivAt_point
  · simpa [ellipsePoint] using ((Real.hasDerivAt_cos t).const_mul a).const_add (C 0)
  · simpa [ellipsePoint] using ((Real.hasDerivAt_sin t).const_mul b).const_add (C 1)

theorem deriv_ellipsePoint (C : Point2D) (a b : ℝ) :
    deriv (ellipsePoint C a b) = fun t => !₂[-a * Real.sin t, b * Real.cos t] :=
  funext fun t => (hasDerivAt_ellipsePoint C a b t).deriv

theorem hasDerivAt_deriv_ellipsePoint (C : Point2D) (a b t : ℝ) :
    HasDerivAt (deriv (ellipsePoint C a b)) !₂[-a * Real.cos t, -b * Real.sin t] t := by
  rw [deriv_ellipsePoint]
  apply hasDerivAt_point
  · simpa using (Real.hasDerivAt_sin t).const_mul (-a)
  · simpa using (Real.hasDerivAt_cos t).const_mul b

/-- Velocity cross acceleration is the constant `a * b`, so the ellipse has no flat point. -/
theorem ellipse_velocityCrossAcceleration (C : Point2D) (a b t : ℝ) :
    velocityCrossAcceleration (ellipsePoint C a b) t = a * b := by
  unfold velocityCrossAcceleration
  rw [(hasDerivAt_deriv_ellipsePoint C a b t).deriv, deriv_ellipsePoint]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination a * b * Real.cos_sq_add_sin_sq t

/-- The centres of curvature of the ellipse, in closed form. -/
theorem ellipse_centerOfCurvature (C : Point2D) (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    centerOfCurvature (ellipsePoint C a b) t =
      C + !₂[(a ^ 2 - b ^ 2) / a * Real.cos t ^ 3, (b ^ 2 - a ^ 2) / b * Real.sin t ^ 3] := by
  unfold centerOfCurvature
  rw [ellipse_velocityCrossAcceleration, deriv_ellipsePoint, point_eq_iff]
  simp only [ellipsePoint, norm_sq_eq_coordinates, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hsin : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := Real.sin_sq t
  have hcos : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := Real.cos_sq' t
  constructor
  · field_simp
    linear_combination -a ^ 2 * Real.cos t * hsin
  · field_simp
    linear_combination -b ^ 2 * Real.sin t * hcos

/-! ### The equation of the evolute -/

private theorem abs_pow_three_rpow (x : ℝ) : (|x| ^ 3) ^ (2 / 3 : ℝ) = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  norm_num

/-- A real cube root, together with its square as a real power. -/
private theorem exists_cube_root (x : ℝ) :
    ∃ p : ℝ, p ^ 3 = x ∧ p ^ 2 = |x| ^ (2 / 3 : ℝ) := by
  have key : ∀ y : ℝ, 0 ≤ y →
      (y ^ (1 / 3 : ℝ)) ^ 3 = y ∧ (y ^ (1 / 3 : ℝ)) ^ 2 = y ^ (2 / 3 : ℝ) := by
    intro y hy
    constructor
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
      norm_num
  rcases le_total 0 x with hx | hx
  · obtain ⟨h3, h2⟩ := key x hx
    exact ⟨x ^ (1 / 3 : ℝ), h3, by rw [h2, abs_of_nonneg hx]⟩
  · obtain ⟨h3, h2⟩ := key (-x) (neg_nonneg.mpr hx)
    refine ⟨-(-x) ^ (1 / 3 : ℝ), ?_, ?_⟩
    · linear_combination -h3
    · rw [neg_sq, h2, abs_of_nonpos hx]

/-- The curve `|u|^(2/3) + |v|^(2/3) = |c|^(2/3)` is traced by `c` times the cubes of
cosine and sine. -/
theorem abs_rpow_add_abs_rpow_eq_iff (c u v : ℝ) :
    |u| ^ (2 / 3 : ℝ) + |v| ^ (2 / 3 : ℝ) = |c| ^ (2 / 3 : ℝ) ↔
      ∃ t : ℝ, u = c * Real.cos t ^ 3 ∧ v = c * Real.sin t ^ 3 := by
  constructor
  · intro h
    obtain ⟨p, hp3, hp2⟩ := exists_cube_root (u / c)
    obtain ⟨q, hq3, hq2⟩ := exists_cube_root (v / c)
    rcases eq_or_ne c 0 with rfl | hc
    · rw [abs_zero, Real.zero_rpow (by norm_num)] at h
      have hu0 : 0 ≤ |u| ^ (2 / 3 : ℝ) := Real.rpow_nonneg (abs_nonneg u) _
      have hv0 : 0 ≤ |v| ^ (2 / 3 : ℝ) := Real.rpow_nonneg (abs_nonneg v) _
      have hu : u = 0 := abs_eq_zero.mp
        ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg u)).mp (by linarith)).1
      have hv : v = 0 := abs_eq_zero.mp
        ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg v)).mp (by linarith)).1
      exact ⟨0, by simp [hu], by simp [hv]⟩
    · have hc0 : 0 < |c| ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (abs_pos.mpr hc) _
      have hunit : p ^ 2 + q ^ 2 = 1 := by
        rw [hp2, hq2, abs_div, abs_div, Real.div_rpow (abs_nonneg u) (abs_nonneg c),
          Real.div_rpow (abs_nonneg v) (abs_nonneg c), ← add_div, h, div_self hc0.ne']
      obtain ⟨t, hcos, hsin⟩ := exists_cos_sin p q hunit
      refine ⟨t, ?_, ?_⟩
      · rw [hcos, hp3, mul_div_cancel₀ u hc]
      · rw [hsin, hq3, mul_div_cancel₀ v hc]
  · rintro ⟨t, rfl, rfl⟩
    rw [abs_mul, abs_mul, abs_pow, abs_pow, Real.mul_rpow (abs_nonneg c) (by positivity),
      Real.mul_rpow (abs_nonneg c) (by positivity), abs_pow_three_rpow, abs_pow_three_rpow,
      ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-! ### Circles through three points of the ellipse -/

/-- The centre of the circle through three points of the ellipse, as a polynomial in
their coordinates. For points at parameters `t₁`, `t₂`, `t₃` it is
`C + ((a² - b²)/(4a) (cos t₁ + cos t₂ + cos t₃ + cos (t₁ + t₂ + t₃)),
(b² - a²)/(4b) (sin t₁ + sin t₂ + sin t₃ - sin (t₁ + t₂ + t₃)))`. -/
def ellipseCircumcenter (C : Point2D) (a b : ℝ) (P₁ P₂ P₃ : Point2D) : Point2D :=
  C + !₂[(a ^ 2 - b ^ 2) / (4 * a) *
      ((P₁ 0 - C 0 + (P₂ 0 - C 0) + (P₃ 0 - C 0)) / a +
        (P₁ 0 - C 0) * (P₂ 0 - C 0) * (P₃ 0 - C 0) / a ^ 3 -
        ((P₁ 0 - C 0) * (P₂ 1 - C 1) * (P₃ 1 - C 1) +
          (P₁ 1 - C 1) * (P₂ 0 - C 0) * (P₃ 1 - C 1) +
          (P₁ 1 - C 1) * (P₂ 1 - C 1) * (P₃ 0 - C 0)) / (a * b ^ 2)),
    (b ^ 2 - a ^ 2) / (4 * b) *
      ((P₁ 1 - C 1 + (P₂ 1 - C 1) + (P₃ 1 - C 1)) / b +
        (P₁ 1 - C 1) * (P₂ 1 - C 1) * (P₃ 1 - C 1) / b ^ 3 -
        ((P₁ 1 - C 1) * (P₂ 0 - C 0) * (P₃ 0 - C 0) +
          (P₁ 0 - C 0) * (P₂ 1 - C 1) * (P₃ 0 - C 0) +
          (P₁ 0 - C 0) * (P₂ 0 - C 0) * (P₃ 1 - C 1)) / (a ^ 2 * b))]

/-- For cosines and sines of `t₁`, `t₂`, `t₃`, this reads
`(Σ cos tᵢ + cos Σ tᵢ) (cos t₁ - cos t₂) - (Σ sin tᵢ - sin Σ tᵢ) (sin t₁ - sin t₂)
= cos 2t₁ - cos 2t₂`. -/
private theorem circle_chord_identity (c₁ s₁ c₂ s₂ c₃ s₃ : ℝ) (h₁ : c₁ ^ 2 + s₁ ^ 2 = 1)
    (h₂ : c₂ ^ 2 + s₂ ^ 2 = 1) :
    (c₁ + c₂ + c₃ + c₁ * c₂ * c₃ - c₁ * s₂ * s₃ - s₁ * c₂ * s₃ - s₁ * s₂ * c₃) * (c₁ - c₂) -
      (s₁ + s₂ + s₃ - s₁ * c₂ * c₃ - c₁ * s₂ * c₃ - c₁ * c₂ * s₃ + s₁ * s₂ * s₃) * (s₁ - s₂) =
      2 * (c₁ ^ 2 - c₂ ^ 2) := by
  linear_combination (c₂ * c₃ - s₂ * s₃ - 1) * h₁ + (-c₁ * c₃ + s₁ * s₃ + 1) * h₂

/-- Sixteen times the squared area of a triangle inscribed in the unit circle is the
product of its squared sides. -/
private theorem circle_area_identity (c₁ s₁ c₂ s₂ c₃ s₃ : ℝ) (h₁ : c₁ ^ 2 + s₁ ^ 2 = 1)
    (h₂ : c₂ ^ 2 + s₂ ^ 2 = 1) (h₃ : c₃ ^ 2 + s₃ ^ 2 = 1) :
    4 * ((c₁ - c₂) * (s₂ - s₃) - (s₁ - s₂) * (c₂ - c₃)) ^ 2 =
      ((c₁ - c₂) ^ 2 + (s₁ - s₂) ^ 2) * ((c₂ - c₃) ^ 2 + (s₂ - s₃) ^ 2) *
        ((c₁ - c₃) ^ 2 + (s₁ - s₃) ^ 2) := by
  grind

private theorem circumcenter_equidistant (a b c₁ s₁ c₂ s₂ c₃ s₃ gx gy : ℝ)
    (h₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (h₂ : c₂ ^ 2 + s₂ ^ 2 = 1) (h₃ : c₃ ^ 2 + s₃ ^ 2 = 1)
    (hgx : 4 * a * gx = (a ^ 2 - b ^ 2) *
      (c₁ + c₂ + c₃ + c₁ * c₂ * c₃ - c₁ * s₂ * s₃ - s₁ * c₂ * s₃ - s₁ * s₂ * c₃))
    (hgy : 4 * b * gy = (b ^ 2 - a ^ 2) *
      (s₁ + s₂ + s₃ - s₁ * c₂ * c₃ - c₁ * s₂ * c₃ - c₁ * c₂ * s₃ + s₁ * s₂ * s₃)) :
    (gx - a * c₁) ^ 2 + (gy - b * s₁) ^ 2 = (gx - a * c₂) ^ 2 + (gy - b * s₂) ^ 2 ∧
      (gx - a * c₂) ^ 2 + (gy - b * s₂) ^ 2 = (gx - a * c₃) ^ 2 + (gy - b * s₃) ^ 2 := by
  constructor
  · linear_combination (-(c₁ - c₂) / 2) * hgx - ((s₁ - s₂) / 2) * hgy -
      ((a ^ 2 - b ^ 2) / 2) * circle_chord_identity c₁ s₁ c₂ s₂ c₃ s₃ h₁ h₂ +
      b ^ 2 * h₁ - b ^ 2 * h₂
  · linear_combination (-(c₂ - c₃) / 2) * hgx - ((s₂ - s₃) / 2) * hgy -
      ((a ^ 2 - b ^ 2) / 2) * circle_chord_identity c₂ s₂ c₃ s₃ c₁ s₁ h₂ h₃ +
      b ^ 2 * h₂ - b ^ 2 * h₃

/-- Three distinct points of an ellipse are not on a line, so only one point is
equidistant from them. -/
private theorem circumcenter_unique (a b c₁ s₁ c₂ s₂ c₃ s₃ gx gy yx yy : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (h₂ : c₂ ^ 2 + s₂ ^ 2 = 1)
    (h₃ : c₃ ^ 2 + s₃ ^ 2 = 1) (h12 : (c₁ - c₂) ^ 2 + (s₁ - s₂) ^ 2 ≠ 0)
    (h23 : (c₂ - c₃) ^ 2 + (s₂ - s₃) ^ 2 ≠ 0) (h13 : (c₁ - c₃) ^ 2 + (s₁ - s₃) ^ 2 ≠ 0)
    (hg12 : (gx - a * c₁) ^ 2 + (gy - b * s₁) ^ 2 = (gx - a * c₂) ^ 2 + (gy - b * s₂) ^ 2)
    (hg23 : (gx - a * c₂) ^ 2 + (gy - b * s₂) ^ 2 = (gx - a * c₃) ^ 2 + (gy - b * s₃) ^ 2)
    (hy12 : (yx - a * c₁) ^ 2 + (yy - b * s₁) ^ 2 = (yx - a * c₂) ^ 2 + (yy - b * s₂) ^ 2)
    (hy23 : (yx - a * c₂) ^ 2 + (yy - b * s₂) ^ 2 = (yx - a * c₃) ^ 2 + (yy - b * s₃) ^ 2) :
    yx = gx ∧ yy = gy := by
  have hΔ : (c₁ - c₂) * (s₂ - s₃) - (s₁ - s₂) * (c₂ - c₃) ≠ 0 := by
    intro h
    have harea := circle_area_identity c₁ s₁ c₂ s₂ c₃ s₃ h₁ h₂ h₃
    rw [h] at harea
    exact mul_ne_zero (mul_ne_zero h12 h23) h13 (by linear_combination -harea)
  have e1 : a * (c₁ - c₂) * (yx - gx) + b * (s₁ - s₂) * (yy - gy) = 0 := by
    linear_combination (1 / 2) * hg12 - (1 / 2) * hy12
  have e2 : a * (c₂ - c₃) * (yx - gx) + b * (s₂ - s₃) * (yy - gy) = 0 := by
    linear_combination (1 / 2) * hg23 - (1 / 2) * hy23
  have hx : a * ((c₁ - c₂) * (s₂ - s₃) - (s₁ - s₂) * (c₂ - c₃)) * (yx - gx) = 0 := by
    linear_combination (s₂ - s₃) * e1 - (s₁ - s₂) * e2
  have hy : b * ((c₁ - c₂) * (s₂ - s₃) - (s₁ - s₂) * (c₂ - c₃)) * (yy - gy) = 0 := by
    linear_combination (c₁ - c₂) * e2 - (c₂ - c₃) * e1
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (mul_ne_zero ha hΔ)),
    sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left (mul_ne_zero hb hΔ))⟩

/-- A point of the ellipse is `C + (a c, b s)` for a point `(c, s)` of the unit circle. -/
private theorem ellipse_unit_coordinates (C P : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : P ∈ ellipse C a b) :
    ∃ c s : ℝ, P 0 = C 0 + a * c ∧ P 1 = C 1 + b * s ∧ c ^ 2 + s ^ 2 = 1 := by
  have hP' : b ^ 2 * (P 0 - C 0) ^ 2 + a ^ 2 * (P 1 - C 1) ^ 2 = a ^ 2 * b ^ 2 := hP
  refine ⟨(P 0 - C 0) / a, (P 1 - C 1) / b, ?_, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ ha]
    ring
  · rw [mul_div_cancel₀ _ hb]
    ring
  · field_simp
    linear_combination hP'

private theorem ellipseCircumcenter_coordinates (C P₁ P₂ P₃ : Point2D)
    (a b c₁ s₁ c₂ s₂ c₃ s₃ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx₁ : P₁ 0 = C 0 + a * c₁) (hy₁ : P₁ 1 = C 1 + b * s₁)
    (hx₂ : P₂ 0 = C 0 + a * c₂) (hy₂ : P₂ 1 = C 1 + b * s₂)
    (hx₃ : P₃ 0 = C 0 + a * c₃) (hy₃ : P₃ 1 = C 1 + b * s₃) :
    4 * a * (ellipseCircumcenter C a b P₁ P₂ P₃ 0 - C 0) = (a ^ 2 - b ^ 2) *
        (c₁ + c₂ + c₃ + c₁ * c₂ * c₃ - c₁ * s₂ * s₃ - s₁ * c₂ * s₃ - s₁ * s₂ * c₃) ∧
      4 * b * (ellipseCircumcenter C a b P₁ P₂ P₃ 1 - C 1) = (b ^ 2 - a ^ 2) *
        (s₁ + s₂ + s₃ - s₁ * c₂ * c₃ - c₁ * s₂ * c₃ - c₁ * c₂ * s₃ + s₁ * s₂ * s₃) := by
  simp only [ellipseCircumcenter, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hx₁, hy₁, hx₂, hy₂, hx₃, hy₃]
  constructor <;> field_simp <;> ring

/-- The polynomial centre is equidistant from the three points of the ellipse. -/
theorem isEquidistant_ellipseCircumcenter (C P₁ P₂ P₃ : Point2D) (a b : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h₁ : P₁ ∈ ellipse C a b) (h₂ : P₂ ∈ ellipse C a b)
    (h₃ : P₃ ∈ ellipse C a b) :
    IsEquidistant (ellipseCircumcenter C a b P₁ P₂ P₃) P₁ P₂ P₃ := by
  obtain ⟨c₁, s₁, hx₁, hy₁, hc₁⟩ := ellipse_unit_coordinates C P₁ a b ha hb h₁
  obtain ⟨c₂, s₂, hx₂, hy₂, hc₂⟩ := ellipse_unit_coordinates C P₂ a b ha hb h₂
  obtain ⟨c₃, s₃, hx₃, hy₃, hc₃⟩ := ellipse_unit_coordinates C P₃ a b ha hb h₃
  obtain ⟨hgx, hgy⟩ := ellipseCircumcenter_coordinates C P₁ P₂ P₃ a b c₁ s₁ c₂ s₂ c₃ s₃ ha hb
    hx₁ hy₁ hx₂ hy₂ hx₃ hy₃
  obtain ⟨e12, e23⟩ := circumcenter_equidistant a b c₁ s₁ c₂ s₂ c₃ s₃ _ _ hc₁ hc₂ hc₃ hgx hgy
  unfold IsEquidistant
  rw [dist_eq_iff_coordinates, dist_eq_iff_coordinates, hx₁, hy₁, hx₂, hy₂, hx₃, hy₃]
  exact ⟨by linear_combination e12, by linear_combination e23⟩

/-- The centre of a circle through three distinct points of the ellipse is the polynomial
centre. -/
theorem eq_ellipseCircumcenter (C P₁ P₂ P₃ Y : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : P₁ ∈ ellipse C a b) (h₂ : P₂ ∈ ellipse C a b) (h₃ : P₃ ∈ ellipse C a b)
    (hY : IsCircumcenter Y P₁ P₂ P₃) :
    Y = ellipseCircumcenter C a b P₁ P₂ P₃ := by
  obtain ⟨h12, h23, h13, hY12, hY23⟩ := hY
  obtain ⟨hG12, hG23⟩ := isEquidistant_ellipseCircumcenter C P₁ P₂ P₃ a b ha hb h₁ h₂ h₃
  obtain ⟨c₁, s₁, hx₁, hy₁, hc₁⟩ := ellipse_unit_coordinates C P₁ a b ha hb h₁
  obtain ⟨c₂, s₂, hx₂, hy₂, hc₂⟩ := ellipse_unit_coordinates C P₂ a b ha hb h₂
  obtain ⟨c₃, s₃, hx₃, hy₃, hc₃⟩ := ellipse_unit_coordinates C P₃ a b ha hb h₃
  have hne : ∀ {P Q : Point2D} {c s c' s' : ℝ}, P ≠ Q → P 0 = C 0 + a * c →
      P 1 = C 1 + b * s → Q 0 = C 0 + a * c' → Q 1 = C 1 + b * s' →
      (c - c') ^ 2 + (s - s') ^ 2 ≠ 0 := by
    intro P Q c s c' s' hPQ hx hy hx' hy' h
    have hc : (c - c') ^ 2 = 0 := by linarith [sq_nonneg (c - c'), sq_nonneg (s - s')]
    have hs : (s - s') ^ 2 = 0 := by linarith [sq_nonneg (c - c'), sq_nonneg (s - s')]
    have hc' : c = c' := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hc)
    have hs' : s = s' := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hs)
    exact hPQ ((point_eq_iff P Q).mpr ⟨by rw [hx, hx', hc'], by rw [hy, hy', hs']⟩)
  rw [dist_eq_iff_coordinates, hx₁, hy₁, hx₂, hy₂] at hY12 hG12
  rw [dist_eq_iff_coordinates, hx₂, hy₂, hx₃, hy₃] at hY23 hG23
  obtain ⟨hx, hy⟩ := circumcenter_unique a b c₁ s₁ c₂ s₂ c₃ s₃
    (ellipseCircumcenter C a b P₁ P₂ P₃ 0 - C 0) (ellipseCircumcenter C a b P₁ P₂ P₃ 1 - C 1)
    (Y 0 - C 0) (Y 1 - C 1) ha hb hc₁ hc₂ hc₃ (hne h12 hx₁ hy₁ hx₂ hy₂)
    (hne h23 hx₂ hy₂ hx₃ hy₃) (hne h13 hx₁ hy₁ hx₃ hy₃)
    (by linear_combination hG12) (by linear_combination hG23)
    (by linear_combination hY12) (by linear_combination hY23)
  exact (point_eq_iff _ _).mpr ⟨by linear_combination hx, by linear_combination hy⟩

/-- When the three points coincide, the polynomial centre is the point given by the
cubes of the coordinates. -/
theorem ellipseCircumcenter_self (C P : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : P ∈ ellipse C a b) :
    ellipseCircumcenter C a b P P P =
      C + !₂[(a ^ 2 - b ^ 2) * (P 0 - C 0) ^ 3 / a ^ 4,
        (b ^ 2 - a ^ 2) * (P 1 - C 1) ^ 3 / b ^ 4] := by
  obtain ⟨c, s, hx, hy, hc⟩ := ellipse_unit_coordinates C P a b ha hb hP
  obtain ⟨hgx, hgy⟩ := ellipseCircumcenter_coordinates C P P P a b c s c s c s ha hb
    hx hy hx hy hx hy
  have h0 : (ellipseCircumcenter C a b P P P 0 - C 0) * a ^ 4 = (a ^ 2 - b ^ 2) * (a * c) ^ 3 := by
    linear_combination (a ^ 3 / 4) * hgx - (3 * (a ^ 2 - b ^ 2) * a ^ 3 * c / 4) * hc
  have h1 : (ellipseCircumcenter C a b P P P 1 - C 1) * b ^ 4 = (b ^ 2 - a ^ 2) * (b * s) ^ 3 := by
    linear_combination (b ^ 3 / 4) * hgy - (3 * (b ^ 2 - a ^ 2) * b ^ 3 * s / 4) * hc
  rw [point_eq_iff]
  simp only [PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hx, hy]
  constructor
  · rw [← sub_eq_iff_eq_add', eq_div_iff (pow_ne_zero 4 ha)]
    linear_combination h0
  · rw [← sub_eq_iff_eq_add', eq_div_iff (pow_ne_zero 4 hb)]
    linear_combination h1

private theorem continuous_ellipseCircumcenter (C : Point2D) (a b : ℝ) :
    Continuous fun q : Point2D × Point2D × Point2D =>
      ellipseCircumcenter C a b q.1 q.2.1 q.2.2 := by
  unfold ellipseCircumcenter
  fun_prop

private theorem continuous_ellipsePoint (C : Point2D) (a b : ℝ) :
    Continuous (ellipsePoint C a b) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_ellipsePoint C a b t).continuousAt

/-- Every point of the ellipse is a limit of other points of the ellipse. -/
private theorem ellipse_mem_closure_diff (C P : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : P ∈ ellipse C a b) : P ∈ closure (ellipse C a b \ {P}) := by
  rw [← range_ellipsePoint C a b ha hb] at hP ⊢
  obtain ⟨t, rfl⟩ := hP
  refine closure_mono ?_ (image_closure_subset_closure_image (continuous_ellipsePoint C a b)
    (Set.mem_image_of_mem _ (?_ : t ∈ closure (Set.Ioo t (t + Real.pi)))))
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, fun h => ?_⟩
    obtain ⟨h0, h1⟩ := (point_eq_iff _ _).mp (Set.mem_singleton_iff.mp h)
    simp only [ellipsePoint, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_right_inj] at h0 h1
    have hcos : Real.cos (s - t) = 1 := by
      rw [Real.cos_sub, mul_left_cancel₀ ha h0, mul_left_cancel₀ hb h1]
      linear_combination Real.cos_sq_add_sin_sq t
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hs.1, Real.pi_pos])
      (by linarith [hs.2, Real.pi_pos])).mp hcos
    linarith [hs.1]
  · rw [closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩

/-- **Circles through three points of an ellipse.** As three points of the ellipse tend
to `P`, the centre of the circle through them tends to the point given by the cubes of
the coordinates of `P`, and to no other point. -/
theorem ellipse_isLimitCircumcenter_iff (C P X : Point2D) (a b : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (hP : P ∈ ellipse C a b) :
    IsLimitCircumcenter (ellipse C a b) P X ↔
      X = C + !₂[(a ^ 2 - b ^ 2) * (P 0 - C 0) ^ 3 / a ^ 4,
        (b ^ 2 - a ^ 2) * (P 1 - C 1) ^ 3 / b ^ 4] := by
  have key : IsLimitCircumcenter (ellipse C a b) P (ellipseCircumcenter C a b P P P) := by
    constructor
    · intro δ hδ
      obtain ⟨Q, ⟨hQ, hQP⟩, dQ⟩ :=
        Metric.mem_closure_iff.mp (ellipse_mem_closure_diff C P a b ha hb hP) δ hδ
      have hPQ : P ≠ Q := fun h => hQP h.symm
      obtain ⟨R, ⟨hR, hRP⟩, dR⟩ := Metric.mem_closure_iff.mp
        (ellipse_mem_closure_diff C P a b ha hb hP) (dist P Q) (dist_pos.mpr hPQ)
      have hPR : P ≠ R := fun h => hRP h.symm
      have hQR : Q ≠ R := fun h => (lt_irrefl _) (h ▸ dR)
      exact ⟨_, P, ⟨hP, Metric.mem_ball_self hδ⟩, Q, ⟨hQ, Metric.mem_ball'.mpr dQ⟩, R,
        ⟨hR, Metric.mem_ball'.mpr (dR.trans dQ)⟩, hPQ, hQR, hPR,
        isEquidistant_ellipseCircumcenter C P Q R a b ha hb hP hQ hR⟩
    · intro ε hε
      obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp
        ((continuous_ellipseCircumcenter C a b).continuousAt (x := (P, P, P))) ε hε
      refine ⟨δ, hδ, ?_⟩
      rintro Y ⟨P₁, ⟨h₁, d₁⟩, P₂, ⟨h₂, d₂⟩, P₃, ⟨h₃, d₃⟩, hY⟩
      rw [eq_ellipseCircumcenter C P₁ P₂ P₃ Y a b ha hb h₁ h₂ h₃ hY]
      exact @hc (P₁, P₂, P₃) (by
        rw [Prod.dist_eq, Prod.dist_eq]
        exact max_lt d₁ (max_lt d₂ d₃))
  rw [← ellipseCircumcenter_self C P a b ha hb hP]
  exact ⟨fun h => h.unique key, by rintro rfl; exact key⟩

/-- At the point of parameter `t`, the limit of the circle centres is the centre of
curvature. -/
theorem ellipse_isLimitCircumcenter_ellipsePoint (C X : Point2D) (a b t : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    IsLimitCircumcenter (ellipse C a b) (ellipsePoint C a b t) X ↔
      centerOfCurvature (ellipsePoint C a b) t = X := by
  have hP : ellipsePoint C a b t ∈ ellipse C a b :=
    range_ellipsePoint C a b ha hb ▸ Set.mem_range_self t
  have hpoint : C + !₂[(a ^ 2 - b ^ 2) * (ellipsePoint C a b t 0 - C 0) ^ 3 / a ^ 4,
        (b ^ 2 - a ^ 2) * (ellipsePoint C a b t 1 - C 1) ^ 3 / b ^ 4] =
      C + !₂[(a ^ 2 - b ^ 2) / a * Real.cos t ^ 3, (b ^ 2 - a ^ 2) / b * Real.sin t ^ 3] := by
    rw [point_eq_iff]
    simp only [ellipsePoint, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    constructor <;> field_simp <;> ring
  rw [ellipse_isLimitCircumcenter_iff C _ X a b ha hb hP, hpoint,
    ellipse_centerOfCurvature C a b t ha hb, eq_comm]

/-- The evolute of the ellipse is traced by the formula for the centre of curvature. -/
theorem mem_evolute_ellipse_iff (C : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (X : Point2D) :
    X ∈ evolute (ellipse C a b) ↔ ∃ t, centerOfCurvature (ellipsePoint C a b) t = X := by
  rw [mem_evolute_iff]
  constructor
  · rintro ⟨P, hP, hX⟩
    rw [← range_ellipsePoint C a b ha hb] at hP
    obtain ⟨t, rfl⟩ := hP
    exact ⟨t, (ellipse_isLimitCircumcenter_ellipsePoint C X a b t ha hb).mp hX⟩
  · rintro ⟨t, hX⟩
    exact ⟨ellipsePoint C a b t, range_ellipsePoint C a b ha hb ▸ Set.mem_range_self t,
      (ellipse_isLimitCircumcenter_ellipsePoint C X a b t ha hb).mpr hX⟩

/-- **The evolute of an ellipse.** A point is on the evolute of the ellipse with centre
`C` and radii `a`, `b` exactly when the stretched astroid expression, with absolute
values under the fractional powers, vanishes there. -/
theorem ellipse_evolute (C : Point2D) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (X : Point2D) :
    X ∈ evolute (ellipse C a b) ↔
      |a * (X 0 - C 0)| ^ (2 / 3 : ℝ) + |b * (X 1 - C 1)| ^ (2 / 3 : ℝ)
        - |a ^ 2 - b ^ 2| ^ (2 / 3 : ℝ) = 0 := by
  rw [sub_eq_zero, ← abs_neg (b * (X 1 - C 1)), abs_rpow_add_abs_rpow_eq_iff,
    mem_evolute_ellipse_iff C a b ha hb]
  refine exists_congr fun t => ?_
  rw [ellipse_centerOfCurvature C a b t ha hb, point_eq_iff]
  simp only [PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h0, h1⟩
    rw [← h0, ← h1]
    constructor <;> field_simp <;> ring
  · rintro ⟨h0, h1⟩
    constructor
    · field_simp
      linear_combination -h0
    · field_simp
      linear_combination h1

end

end SympyGeometry
