module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic

/-!
# The real cubic surd

Define the cube root as a function `ℝ → ℝ`, using real powers of nonnegative
numbers, and prove its cube equation, uniqueness, and compatibility with
negation. It is real analytic exactly at the nonzero inputs and is not
differentiable at zero. These proofs use the real logarithm and exponential;
the complex cube-root extensions are defined separately in `CubicSurd.lean`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Filter
open scoped Topology

/-- The usual real cube root, expressed using nonnegative real powers. -/
def realCubicSurd (x : ℝ) : ℝ :=
  if x < 0 then -((-x) ^ (3⁻¹ : ℝ)) else x ^ (3⁻¹ : ℝ)

@[simp] theorem realCubicSurd_cube (x : ℝ) : realCubicSurd x ^ 3 = x := by
  unfold realCubicSurd
  split_ifs with hx
  · have h : ((-x) ^ (3⁻¹ : ℝ)) ^ 3 = -x :=
      Real.rpow_inv_natCast_pow (by linarith) (by decide : 3 ≠ 0)
    calc
      (-((-x) ^ (3⁻¹ : ℝ))) ^ 3 = -(((-x) ^ (3⁻¹ : ℝ)) ^ 3) := by ring
      _ = x := by rw [h]; exact neg_neg x
  · exact Real.rpow_inv_natCast_pow (le_of_not_gt hx) (by decide : 3 ≠ 0)

theorem realCubicSurd_unique {x y : ℝ} (hy : y ^ 3 = x) : y = realCubicSurd x :=
  (show Odd (3 : ℕ) by decide).pow_injective (hy.trans (realCubicSurd_cube x).symm)

@[simp] theorem realCubicSurd_neg (x : ℝ) : realCubicSurd (-x) = -realCubicSurd x := by
  symm
  apply realCubicSurd_unique
  calc
    (-realCubicSurd x) ^ 3 = -(realCubicSurd x ^ 3) := by ring
    _ = -x := by rw [realCubicSurd_cube]

@[simp] theorem realCubicSurd_zero : realCubicSurd 0 = 0 :=
  eq_zero_of_pow_eq_zero (realCubicSurd_cube 0)

/-- On the positive half-line, use the real analytic formula `exp (log x / 3)`. -/
theorem analyticAt_realCubicSurd_of_pos {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ realCubicSurd x := by
  have heq : realCubicSurd =ᶠ[𝓝 x] (fun y : ℝ => Real.exp (Real.log y * (3⁻¹ : ℝ))) := by
    filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
    change 0 < y at hy
    simp only [realCubicSurd, not_lt.mpr hy.le, ↓reduceIte, Real.rpow_def_of_pos hy]
  have ha : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y * (3⁻¹ : ℝ))) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp'
  exact ha.congr heq.symm

/-- The real cube root is real analytic at every nonzero input, including negative inputs. -/
theorem analyticAt_realCubicSurd {x : ℝ} (hx : x ≠ 0) : AnalyticAt ℝ realCubicSurd x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have ha : AnalyticAt ℝ (fun y : ℝ => -realCubicSurd (-y)) x :=
      ((analyticAt_realCubicSurd_of_pos (neg_pos.mpr hn)).comp analyticAt_id.neg).neg
    simpa only [realCubicSurd_neg, neg_neg] using ha
  · exact analyticAt_realCubicSurd_of_pos hp

theorem analyticOnNhd_realCubicSurd : AnalyticOnNhd ℝ realCubicSurd {x : ℝ | x ≠ 0} :=
  fun _ hx => analyticAt_realCubicSurd hx

/-- Differentiating `realCubicSurd(x)^3 = x` at zero would give `0 = 1`. -/
theorem not_differentiableAt_realCubicSurd_zero : ¬DifferentiableAt ℝ realCubicSurd 0 := by
  intro hd
  have h := hd.hasDerivAt.fun_pow 3
  have hid : HasDerivAt (fun x : ℝ => x) 0 0 := by
    simpa only [Pi.pow_apply, realCubicSurd_cube, realCubicSurd_zero, Nat.cast_ofNat,
      show 3 - 1 = 2 by decide, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using h
  have := hid.unique (hasDerivAt_id (0 : ℝ))
  norm_num at this

theorem not_analyticAt_realCubicSurd_zero : ¬AnalyticAt ℝ realCubicSurd 0 :=
  fun h => not_differentiableAt_realCubicSurd_zero h.differentiableAt

/-- An exact characterization of the real analytic points. -/
theorem analyticAt_realCubicSurd_iff {x : ℝ} : AnalyticAt ℝ realCubicSurd x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    exact not_analyticAt_realCubicSurd_zero h
  · exact analyticAt_realCubicSurd

end RealCubeRoot
