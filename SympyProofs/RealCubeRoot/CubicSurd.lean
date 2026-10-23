module

public import SympyProofs.RealCubeRoot.RealCubicSurd
public import SympyProofs.RealCubeRoot.Principal

/-!
# The cubic surd extending the real cubic surd

The real function and its uniqueness proof are defined in `RealCubicSurd.lean`.
The principal cube root and its supporting proofs are in `Principal.lean`.
`cubicSurd : ℂ → ℂ` extends `realCubicSurd` on every real input, including zero.
The cube-root equation is asserted on `domain`, which excludes only the
nonzero imaginary-axis points. Analyticity is asserted on the smaller open set
`analyticDomain`. Values outside `domain` are zero placeholders.
Total extensions with specified boundary values live in `Extensions.lean`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex
open scoped ComplexConjugate

/-- The open set on which the cubic surd is complex analytic. -/
def analyticDomain : Set ℂ := {z | z.re ≠ 0}

/-- The set on which the cubic surd satisfies its cube-root equation. -/
def domain : Set ℂ := {z | z.re ≠ 0 ∨ z = 0}

theorem analyticDomain_subset_domain : analyticDomain ⊆ domain :=
  fun _ hz => Or.inl hz

@[simp] theorem zero_mem_domain : (0 : ℂ) ∈ domain := Or.inr rfl

/-- Every real input, including zero, belongs to the domain. -/
@[simp] theorem ofReal_mem_domain (x : ℝ) : (x : ℂ) ∈ domain := by
  by_cases hx : x = 0
  · simp [hx]
  · exact Or.inl hx

/-- The complex extension of `realCubicSurd`, satisfying the cube-root equation on
`domain`. Values at nonzero imaginary-axis points are zero placeholders. -/
def cubicSurd (z : ℂ) : ℂ :=
  if z.re = 0 then 0 else if z.re < 0 then -principal (-z) else principal z

theorem cubicSurd_eq_principal {z : ℂ} (hz : 0 < z.re) :
    cubicSurd z = principal z := by
  simp [cubicSurd, ne_of_gt hz, not_lt.mpr hz.le]

theorem cubicSurd_eq_neg_principal {z : ℂ} (hz : z.re < 0) :
    cubicSurd z = -principal (-z) := by
  simp [cubicSurd, ne_of_lt hz, hz]

@[simp] theorem cubicSurd_zero : cubicSurd 0 = 0 := by
  simp [cubicSurd]

@[simp] theorem cubicSurd_cube {z : ℂ} (hz : z ∈ domain) :
    cubicSurd z ^ 3 = z := by
  rcases hz with hz | rfl
  · rcases lt_or_gt_of_ne hz with hn | hp
    · rw [cubicSurd_eq_neg_principal hn, neg_pow, principal_cube]
      norm_num
    · rw [cubicSurd_eq_principal hp, principal_cube]
  · simp

@[simp] theorem cubicSurd_one : cubicSurd 1 = 1 := by
  simp [cubicSurd, principal]

@[simp] theorem cubicSurd_neg_one : cubicSurd (-1) = -1 := by
  norm_num [cubicSurd, principal]

/-- The logarithmic formula on the right half-plane. -/
theorem cubicSurd_eq_exp_log {z : ℂ} (hz : 0 < z.re) :
    cubicSurd z = exp (log z / 3) := by
  rw [cubicSurd_eq_principal hz, principal,
    Complex.cpow_def_of_ne_zero (fun h => by simp [h] at hz)]
  rfl

/-- The logarithmic formula on the left half-plane, including negative reals. -/
theorem cubicSurd_eq_neg_exp_log {z : ℂ} (hz : z.re < 0) :
    cubicSurd z = -exp (log (-z) / 3) := by
  rw [cubicSurd_eq_neg_principal hz, principal,
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr (fun h => by simp [h] at hz))]
  rfl

@[simp] theorem cubicSurd_conj (z : ℂ) :
    cubicSurd (conj z) = conj (cubicSurd z) := by
  by_cases hz : z.re = 0
  · simp [cubicSurd, hz]
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hs : -z ∈ slitPlane := Or.inl (by simpa using neg_pos.mpr hn)
    simpa only [cubicSurd, conj_re, hz, hn, ↓reduceIte, map_neg] using
      congrArg Neg.neg (principal_conj_of_mem_slitPlane hs)
  · have hs : z ∈ slitPlane := Or.inl hp
    simpa only [cubicSurd, conj_re, hz, not_lt.mpr hp.le, ↓reduceIte] using
      principal_conj_of_mem_slitPlane hs

@[simp] theorem conj_mem_analyticDomain_iff (z : ℂ) :
    conj z ∈ analyticDomain ↔ z ∈ analyticDomain := by
  simp [analyticDomain]

@[simp] theorem conj_mem_domain_iff (z : ℂ) : conj z ∈ domain ↔ z ∈ domain := by
  simp [domain]

/-- Agreement with the real cubic surd holds for all real inputs, including zero. -/
@[simp] theorem cubicSurd_ofReal (x : ℝ) :
    cubicSurd (x : ℂ) = (realCubicSurd x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp
  unfold cubicSurd realCubicSurd principal
  simp only [Complex.ofReal_re, hx, ↓reduceIte]
  by_cases hn : x < 0
  · simp only [hn, ↓reduceIte, Complex.ofReal_neg]
    congr 1
    simpa using (Complex.ofReal_cpow (by linarith : 0 ≤ -x) (3⁻¹ : ℝ)).symm
  · simp only [hn, ↓reduceIte]
    simpa using (Complex.ofReal_cpow (le_of_not_gt hn) (3⁻¹ : ℝ)).symm

end RealCubeRoot
