module

public import SympyProofs.RealCubeRoot.Analytic

/-!
# Two total extensions of the analytic real cube-root branch

`cubicSurdRight` takes right-half-plane boundary values on the imaginary axis;
`cubicSurdLeft` takes left-half-plane boundary values. Both agree with `cubicSurd` on
`domain` and commute with conjugation everywhere. The direct real-coefficient
Cardano formula uses the right-side extension.
One-sided continuity is proved in `Boundary.lean`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex Filter
open scoped ComplexConjugate Topology

/-- The total extension taking right-half-plane values on the cut. -/
def cubicSurdRight (z : ℂ) : ℂ :=
  if z.re < 0 then -principal (-z) else principal z

/-- The total extension taking left-half-plane values on the cut. -/
def cubicSurdLeft (z : ℂ) : ℂ := -cubicSurdRight (-z)

@[simp] theorem cubicSurdRight_cube (z : ℂ) : cubicSurdRight z ^ 3 = z := by
  unfold cubicSurdRight
  split_ifs
  · rw [neg_pow, principal_cube]
    norm_num
  · exact principal_cube z

@[simp] theorem cubicSurdRight_zero : cubicSurdRight 0 = 0 := by
  simp [cubicSurdRight, principal]

@[simp] theorem cubicSurdRight_one : cubicSurdRight 1 = 1 := by
  simp [cubicSurdRight, principal]

@[simp] theorem cubicSurdRight_neg_one : cubicSurdRight (-1) = -1 := by
  norm_num [cubicSurdRight, principal]

theorem cubicSurdRight_ne_zero {z : ℂ} (hz : z ≠ 0) : cubicSurdRight z ≠ 0 := by
  intro h
  have := cubicSurdRight_cube z
  simp [h] at this
  exact hz this.symm

theorem cubicSurdRight_eq_principal {z : ℂ} (hz : 0 ≤ z.re) : cubicSurdRight z = principal z := by
  simp [cubicSurdRight, not_lt.mpr hz]

theorem cubicSurdRight_eq_neg_principal {z : ℂ} (hz : z.re < 0) :
    cubicSurdRight z = -principal (-z) := by
  simp [cubicSurdRight, hz]

/-- The logarithmic formula on the right half-plane. -/
theorem cubicSurdRight_eq_exp_log {z : ℂ} (hz : 0 < z.re) :
    cubicSurdRight z = exp (log z / 3) := by
  rw [cubicSurdRight_eq_principal hz.le, principal,
    Complex.cpow_def_of_ne_zero (fun h => by simp [h] at hz)]
  rfl

/-- The logarithmic formula on the left half-plane, including negative reals. -/
theorem cubicSurdRight_eq_neg_exp_log {z : ℂ} (hz : z.re < 0) :
    cubicSurdRight z = -exp (log (-z) / 3) := by
  rw [cubicSurdRight_eq_neg_principal hz, principal,
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr (fun h => by simp [h] at hz))]
  rfl

/-- On every real input, including zero and negative inputs, this is the real cube root. -/
@[simp] theorem cubicSurdRight_ofReal (x : ℝ) : cubicSurdRight (x : ℂ) = (realCubicSurd x : ℂ) := by
  unfold cubicSurdRight realCubicSurd principal
  by_cases hx : x < 0
  · simp only [Complex.ofReal_re, hx, ↓reduceIte, Complex.ofReal_neg]
    congr 1
    simpa using (Complex.ofReal_cpow (by linarith : 0 ≤ -x) (3⁻¹ : ℝ)).symm
  · simp only [Complex.ofReal_re, hx, ↓reduceIte]
    simpa using (Complex.ofReal_cpow (le_of_not_gt hx) (3⁻¹ : ℝ)).symm

/-- Conjugation commutes even with the chosen values on the cut. -/
@[simp] theorem cubicSurdRight_conj (z : ℂ) : cubicSurdRight (conj z) = conj (cubicSurdRight z) := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hneg : z.re < 0
  · have hs : -z ∈ slitPlane := Or.inl (by simpa using neg_pos.mpr hneg)
    simpa only [cubicSurdRight, conj_re, hneg, ↓reduceIte, map_neg] using
      congrArg Neg.neg (principal_conj_of_mem_slitPlane hs)
  · have hs : z ∈ slitPlane := by
      rcases lt_or_eq_of_le (le_of_not_gt hneg) with hpos | hzero
      · exact Or.inl hpos
      · exact Or.inr (fun him => hz (Complex.ext hzero.symm him))
    simpa only [cubicSurdRight, conj_re, hneg, ↓reduceIte] using
      principal_conj_of_mem_slitPlane hs

/-- A direct realness certificate for a pair of conjugate cube-root arguments. -/
theorem cubicSurdRight_add_conj (z : ℂ) :
    cubicSurdRight z + cubicSurdRight (conj z) = (2 * (cubicSurdRight z).re : ℝ) := by
  rw [cubicSurdRight_conj]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The right-side extension restricts to the basic branch. -/
theorem cubicSurdRight_eq_cubicSurd : Set.EqOn cubicSurdRight cubicSurd domain := by
  intro z hz
  rcases hz with hz | rfl
  · simp only [cubicSurd, hz, ↓reduceIte, cubicSurdRight]
  · simpa only [cubicSurd_zero] using cubicSurdRight_zero

/-- At a right-half-plane point, the branch agrees locally with the principal root. -/
theorem eventuallyEq_cubicSurdRight_principal {z : ℂ} (hz : 0 < z.re) :
    cubicSurdRight =ᶠ[𝓝 z] principal := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
    with w hw
  exact cubicSurdRight_eq_principal (le_of_lt hw)

/-- At a left-half-plane point, the branch agrees locally with the reflected root. -/
theorem eventuallyEq_cubicSurdRight_neg_principal {z : ℂ} (hz : z.re < 0) :
    cubicSurdRight =ᶠ[𝓝 z] (fun w => -principal (-w)) := by
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz]
    with w hw
  exact cubicSurdRight_eq_neg_principal hw

theorem analyticAt_cubicSurdRight {z : ℂ} (hz : z ∈ analyticDomain) : AnalyticAt ℂ cubicSurdRight z := by
  have heq : cubicSurdRight =ᶠ[𝓝 z] cubicSurd := by
    filter_upwards [isOpen_analyticDomain.mem_nhds hz] with w hw
    exact cubicSurdRight_eq_cubicSurd (analyticDomain_subset_domain hw)
  exact (analyticAt_cubicSurd hz).congr heq.symm

theorem analyticOnNhd_cubicSurdRight : AnalyticOnNhd ℂ cubicSurdRight analyticDomain :=
  fun _ hz => analyticAt_cubicSurdRight hz

theorem differentiableOn_cubicSurdRight : DifferentiableOn ℂ cubicSurdRight analyticDomain :=
  analyticOnNhd_cubicSurdRight.differentiableOn

theorem continuousOn_cubicSurdRight : ContinuousOn cubicSurdRight domain :=
  continuousOn_cubicSurd.congr cubicSurdRight_eq_cubicSurd

/-- In particular, the real branch is analytic at every nonzero real input. -/
theorem analyticAt_cubicSurdRight_ofReal {x : ℝ} (hx : x ≠ 0) :
    AnalyticAt ℂ cubicSurdRight (x : ℂ) :=
  analyticAt_cubicSurdRight hx

/-- The derivative is the one forced by the cube-root equation. -/
theorem deriv_cubicSurdRight {z : ℂ} (hz : z ∈ analyticDomain) :
    deriv cubicSurdRight z = 1 / (3 * cubicSurdRight z ^ 2) := by
  have h := (analyticAt_cubicSurdRight hz).differentiableAt.hasDerivAt.fun_pow 3
  have hid : HasDerivAt (fun w : ℂ => w) (3 * cubicSurdRight z ^ 2 * deriv cubicSurdRight z) z := by
    simpa only [Pi.pow_apply, cubicSurdRight_cube, Nat.cast_ofNat, show 3 - 1 = 2 by decide] using h
  have heq := hid.unique (hasDerivAt_id z)
  have hne : cubicSurdRight z ≠ 0 := cubicSurdRight_ne_zero (fun h => hz (by simp [h]))
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hne))).mpr
  simpa only [mul_comm] using heq

theorem not_analyticAt_cubicSurdRight_zero : ¬AnalyticAt ℂ cubicSurdRight 0 :=
  fun h => not_differentiableAt_zero_of_cube cubicSurdRight_cube h.differentiableAt

@[simp] theorem cubicSurdLeft_cube (z : ℂ) : cubicSurdLeft z ^ 3 = z := by
  unfold cubicSurdLeft
  rw [neg_pow, cubicSurdRight_cube]
  norm_num

@[simp] theorem cubicSurdLeft_conj (z : ℂ) :
    cubicSurdLeft (conj z) = conj (cubicSurdLeft z) := by
  simp [cubicSurdLeft, ← map_neg]

@[simp] theorem cubicSurdLeft_ofReal (x : ℝ) :
    cubicSurdLeft (x : ℂ) = (realCubicSurd x : ℂ) := by
  unfold cubicSurdLeft
  rw [← Complex.ofReal_neg, cubicSurdRight_ofReal, realCubicSurd_neg, Complex.ofReal_neg, neg_neg]

theorem cubicSurdLeft_eq_principal {z : ℂ} (hz : 0 < z.re) :
    cubicSurdLeft z = principal z := by
  simp [cubicSurdLeft, cubicSurdRight, neg_lt_zero.mpr hz]

theorem cubicSurdLeft_eq_neg_principal {z : ℂ} (hz : z.re ≤ 0) :
    cubicSurdLeft z = -principal (-z) := by
  simp [cubicSurdLeft, cubicSurdRight, not_lt.mpr (neg_nonneg.mpr hz)]

/-- The left-side extension restricts to the same basic branch. -/
theorem cubicSurdLeft_eq_cubicSurd : Set.EqOn cubicSurdLeft cubicSurd domain := by
  intro z hz
  rcases hz with hz | rfl
  · rcases lt_or_gt_of_ne hz with hn | hp
    · rw [cubicSurdLeft_eq_neg_principal hn.le, cubicSurd_eq_neg_principal hn]
    · rw [cubicSurdLeft_eq_principal hp, cubicSurd_eq_principal hp]
  · simp [cubicSurdLeft, cubicSurdRight, principal]

theorem analyticOnNhd_cubicSurdLeft : AnalyticOnNhd ℂ cubicSurdLeft analyticDomain := by
  intro z hz
  have heq : cubicSurdLeft =ᶠ[𝓝 z] cubicSurd := by
    filter_upwards [isOpen_analyticDomain.mem_nhds hz] with w hw
    exact cubicSurdLeft_eq_cubicSurd (analyticDomain_subset_domain hw)
  exact (analyticAt_cubicSurd hz).congr heq.symm

theorem not_analyticAt_cubicSurdLeft_zero : ¬AnalyticAt ℂ cubicSurdLeft 0 :=
  fun h => not_differentiableAt_zero_of_cube cubicSurdLeft_cube h.differentiableAt

end RealCubeRoot
