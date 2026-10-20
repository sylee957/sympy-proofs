module

public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# One-dimensional minimization for plane distances

The signed plane residual along a segment is `(1 - t) * a + t * b`, and
along a ray or line it is `a + t * c`. These results include zero slopes and zero
residuals. The segment formula is continuous and uses only absolute values.
The ray and line formulas use `sign`; the ray formula's discontinuity at a
parallel ray is unavoidable.
-/

@[expose] public section

namespace SympyGeometry

/-- Minimum absolute residual along a closed segment, without a slope denominator. -/
noncomputable def segmentValue (a b : ℝ) : ℝ :=
  (|a| + |b| - |b - a|) / 2

/-- Minimum absolute residual along a ray. The strict inequality includes the
parallel case in the second branch. -/
noncomputable def rayValue (a c : ℝ) : ℝ :=
  if a * c < 0 then 0 else |a|

/-- Minimum absolute residual along a line, expressed using `sign`. -/
noncomputable def lineValue (a c : ℝ) : ℝ :=
  |a| * (1 - |Real.sign c|)

theorem segmentValue_nonneg (a b : ℝ) : 0 ≤ segmentValue a b := by
  have h := abs_sub b a
  dsimp [segmentValue]
  linarith

/-- A lower bound at every point of the segment. -/
theorem segmentValue_le (a b t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentValue a b ≤ |(1 - t) * a + t * b| := by
  have ha : |a| ≤ |(1 - t) * a + t * b| + t * |b - a| := calc
    |a| = |((1 - t) * a + t * b) - t * (b - a)| := by congr 1; ring
    _ ≤ |(1 - t) * a + t * b| + |t * (b - a)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg ht.1]
  have hb : |b| ≤ |(1 - t) * a + t * b| + (1 - t) * |b - a| := calc
    |b| = |((1 - t) * a + t * b) + (1 - t) * (b - a)| := by congr 1; ring
    _ ≤ |(1 - t) * a + t * b| + |(1 - t) * (b - a)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  dsimp [segmentValue]
  nlinarith

/-- The lower bound is attained, including when the endpoints coincide. -/
theorem segmentValue_attained (a b : ℝ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, |(1 - t) * a + t * b| = segmentValue a b := by
  have hc : ContinuousOn (fun t : ℝ => (1 - t) * a + t * b) (Set.Icc 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => (1 - t) * a + t * b)).continuousOn
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rcases le_total a b with hab | hab
    · refine ⟨0, by norm_num, ?_⟩
      simp only [segmentValue, zero_mul, sub_zero, one_mul, add_zero,
        abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (sub_nonneg.mpr hab)]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      simp only [segmentValue, sub_self, zero_mul, one_mul, zero_add,
        abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
  · obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Set.Icc ((1 - 1) * a + 1 * b) ((1 - 0) * a + 0 * b) by
        simpa using And.intro hb ha)
    refine ⟨t, ht, ?_⟩
    dsimp only at he
    rw [he, abs_zero]
    dsimp [segmentValue]
    rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonpos (by linarith : b - a ≤ 0)]
    ring
  · obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Set.Icc ((1 - 0) * a + 0 * b) ((1 - 1) * a + 1 * b) by
        simpa using And.intro ha hb)
    refine ⟨t, ht, ?_⟩
    dsimp only at he
    rw [he, abs_zero]
    dsimp [segmentValue]
    rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonneg (by linarith : 0 ≤ b - a)]
    ring
  · rcases le_total a b with hab | hab
    · refine ⟨1, by norm_num, ?_⟩
      simp only [segmentValue, sub_self, zero_mul, one_mul, zero_add,
        abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonneg (sub_nonneg.mpr hab)]
      ring
    · refine ⟨0, by norm_num, ?_⟩
      simp only [segmentValue, zero_mul, sub_zero, one_mul, add_zero,
        abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring

theorem rayValue_nonneg (a c : ℝ) : 0 ≤ rayValue a c := by
  unfold rayValue
  split_ifs <;> positivity

/-- A lower bound at every point of the ray. -/
theorem rayValue_le (a c t : ℝ) (ht : 0 ≤ t) :
    rayValue a c ≤ |a + t * c| := by
  unfold rayValue
  split_ifs with hac
  · exact abs_nonneg _
  · have hac' : 0 ≤ a * c := le_of_not_gt hac
    have hsq : a ^ 2 ≤ (a + t * c) ^ 2 := by
      nlinarith [mul_nonneg ht hac', sq_nonneg (t * c)]
    nlinarith [sq_abs a, sq_abs (a + t * c), abs_nonneg a, abs_nonneg (a + t * c)]

/-- A closest parameter exists even for a parallel ray or a zero direction. -/
theorem rayValue_attained (a c : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ |a + t * c| = rayValue a c := by
  by_cases hac : a * c < 0
  · have hc : c ≠ 0 := by intro h; simp [h] at hac
    have ht : 0 ≤ -a / c := by
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · exact div_nonneg_of_nonpos (by nlinarith) hc'.le
      · exact div_nonneg (by nlinarith) hc'.le
    refine ⟨-a / c, ht, ?_⟩
    rw [div_mul_cancel₀ _ hc, add_neg_cancel, abs_zero, rayValue, ite_eq_left hac]
  · exact ⟨0, le_rfl, by simp [rayValue, hac]⟩

/-- A single expression with no division by the normal component of the direction.
`Real.sign 0 = 0`, so parallel rays retain their full starting distance. -/
theorem rayValue_eq_sign (a c : ℝ) :
    rayValue a c = |a| * (1 + min 0 (Real.sign (a * c))) := by
  rcases lt_trichotomy (a * c) 0 with h | h | h
  · simp [rayValue, h, Real.sign_of_neg h]
  · simp [rayValue, h]
  · simp [rayValue, not_lt.mpr h.le, Real.sign_of_pos h]

/-- A zero slope leaves the residual constant along the line. -/
@[simp] theorem lineValue_zero (a : ℝ) : lineValue a 0 = |a| := by
  simp [lineValue]

/-- Every nonzero slope lets the line reach residual zero. -/
theorem lineValue_of_ne_zero (a c : ℝ) (hc : c ≠ 0) : lineValue a c = 0 := by
  rcases Real.sign_apply_eq_of_ne_zero c hc with hs | hs <;> simp [lineValue, hs]

theorem lineValue_nonneg (a c : ℝ) : 0 ≤ lineValue a c := by
  rcases Real.sign_apply_eq c with hs | hs | hs <;> simp [lineValue, hs]

/-- A lower bound at every point of the line, with no restriction on the parameter. -/
theorem lineValue_le (a c t : ℝ) : lineValue a c ≤ |a + t * c| := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [lineValue_of_ne_zero a c hc]
    exact abs_nonneg _

/-- A closest parameter exists even when the line is parallel or has zero direction. -/
theorem lineValue_attained (a c : ℝ) :
    ∃ t : ℝ, |a + t * c| = lineValue a c := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  · exact ⟨-a / c, by rw [div_mul_cancel₀ _ hc, add_neg_cancel, abs_zero,
      lineValue_of_ne_zero a c hc]⟩

/-- The exact ray distance is discontinuous as its normal slope passes through zero.
Consequently, everywhere-defined continuous arithmetic operations cannot express it. -/
theorem rayValue_not_continuousAt_parallel :
    ¬ ContinuousAt (fun c : ℝ => rayValue 1 c) 0 := by
  intro h
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp h (1 / 2) (by norm_num)
  have hn : -δ / 2 < 0 := by linarith
  have hnear : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hn]
    linarith
  have hbad := hclose hnear
  norm_num [rayValue, hn, Real.dist_eq] at hbad

end SympyGeometry
