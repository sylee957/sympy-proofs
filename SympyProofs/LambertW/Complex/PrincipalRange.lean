import SympyProofs.LambertW.Complex.Geometry

/-!
# The principal output region

The proposed principal range lies between imaginary parts `-π` and `π`, to
the right of the quadratrix boundary. On the real axis it consists of `(-1, ∞)`.
We prove that `mulExp` maps this region into the principal slit domain.
Surjectivity and injectivity are not asserted here.
-/

namespace LambertW.Complex

open Set

/-- The output region for the principal inverse on the open slit domain.
The real-axis clause uses the limiting quadratrix boundary value `-1`. -/
def principalRange : Set ℂ := {w |
  w.im ∈ Ioo (-Real.pi) Real.pi ∧
  (w.im = 0 → -1 < w.re) ∧
  (w.im ≠ 0 → -w.im * Real.cos w.im / Real.sin w.im < w.re)}

@[simp] theorem ofReal_mem_principalRange (x : ℝ) :
    (x : ℂ) ∈ principalRange ↔ -1 < x := by
  simp [principalRange, Real.pi_pos]

@[simp] theorem zero_mem_principalRange : (0 : ℂ) ∈ principalRange := by
  simpa using (ofReal_mem_principalRange 0).mpr (by norm_num)

theorem neg_one_notMem_principalRange : (-1 : ℂ) ∉ principalRange := by
  simpa using (ofReal_mem_principalRange (-1))

/-- In the upper part of the principal region, the forward image is in the upper half-plane. -/
theorem mulExp_im_pos_of_mem_principalRange {w : ℂ}
    (hw : w ∈ principalRange) (hi : 0 < w.im) : 0 < (mulExp w).im := by
  have hs : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi hi hw.1.2
  have hb := (div_lt_iff₀ hs).mp (hw.2.2 (ne_of_gt hi))
  rw [mulExp_im]
  apply mul_pos (Real.exp_pos _)
  nlinarith

/-- In the lower part of the principal region, the forward image is in the lower half-plane. -/
theorem mulExp_im_neg_of_mem_principalRange {w : ℂ}
    (hw : w ∈ principalRange) (hi : w.im < 0) : (mulExp w).im < 0 := by
  have hs : Real.sin w.im < 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hi)
      (show -w.im < Real.pi by linarith [hw.1.1])
    simpa using h
  have hb := (div_lt_iff_of_neg hs).mp (hw.2.2 (ne_of_lt hi))
  rw [mulExp_im]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  nlinarith

/-- The proposed principal range maps into the open principal slit domain. -/
theorem mulExp_mapsTo_principalDomain : MapsTo mulExp principalRange principalDomain := by
  intro w hw
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · exact Or.inl (ne_of_lt (mulExp_im_neg_of_mem_principalRange hw hi))
  · right
    have hr : -1 < w.re := hw.2.1 hi
    have h := Real.strictMonoOn_mulExp
      (show (-1 : ℝ) ∈ Ici (-1) by simp) hr.le hr
    have heq : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    rw [heq, mulExp_ofReal, Complex.ofReal_re]
    simpa using h
  · exact Or.inl (ne_of_gt (mulExp_im_pos_of_mem_principalRange hw hi))

/-- There are no critical points in the principal output region. -/
theorem deriv_mulExp_ne_zero_of_mem_principalRange {w : ℂ}
    (hw : w ∈ principalRange) : deriv mulExp w ≠ 0 :=
  deriv_mulExp_ne_zero_of_mem_principalDomain (mulExp_mapsTo_principalDomain hw)

/-- A nonreal quadratrix point is excluded by the strict boundary inequality. -/
theorem quadratrix_notMem_principalRange {t : ℝ} (ht : t ≠ 0) :
    quadratrix t ∉ principalRange := by
  intro h
  have hb := h.2.2 (by simpa using ht)
  simp at hb

/-- A point in the principal region maps to the real axis exactly when it is real. -/
theorem mulExp_im_eq_zero_iff_of_mem_principalRange {w : ℂ}
    (hw : w ∈ principalRange) : (mulExp w).im = 0 ↔ w.im = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy w.im 0 with hi | hi | hi
    · exact False.elim ((ne_of_lt (mulExp_im_neg_of_mem_principalRange hw hi)) h)
    · exact hi
    · exact False.elim ((ne_of_gt (mulExp_im_pos_of_mem_principalRange hw hi)) h)
  · intro h
    simp [mulExp_im, h]

/-- On real inputs in the slit domain, the unique principal-region preimage is already known. -/
theorem existsUnique_principalRange_mulExp_ofReal {x : ℝ}
    (hx : -Real.exp (-1) < x) :
    ∃! w : ℂ, w ∈ principalRange ∧ mulExp w = (x : ℂ) := by
  have hp : -1 < Real.principal x := by
    have h := Real.strictMonoOn_principal
      (show -Real.exp (-1) ∈ Ici (-Real.exp (-1)) by simp) hx.le hx
    simpa using h
  refine ⟨(Real.principal x : ℂ), ⟨(ofReal_mem_principalRange _).mpr hp, ?_⟩, ?_⟩
  · rw [mulExp_ofReal, Real.mulExp_principal hx.le]
  · intro w hw
    have hi : w.im = 0 := (mulExp_im_eq_zero_iff_of_mem_principalRange hw.1).mp (by
      rw [hw.2, Complex.ofReal_im])
    have heq : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have hf : Real.mulExp w.re = x := by
      have h := hw.2
      rw [heq, mulExp_ofReal] at h
      exact Complex.ofReal_injective h
    have hr : w.re = Real.principal x :=
      Real.strictMonoOn_mulExp.injOn (hw.1.2.1 hi).le hp.le
        (hf.trans (Real.mulExp_principal hx.le).symm)
    rw [heq, hr]

end LambertW.Complex
