import SympyProofs.ComplexRouthHurwitz.Table.Rows

/-! Counts used by the direct complex table, including imaginary-axis roots. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

/-- Open-left-half-plane roots, counted with multiplicity. -/
def leftCount (p : ℂ[X]) : ℕ := regionCount p (fun z => z.re < 0)

theorem counts_partition (p : ℂ[X]) :
    rightCount p + leftCount p + axisCount p = p.natDegree := by
  rw [(IsAlgClosed.splits p).natDegree_eq_card_roots]
  unfold rightCount leftCount axisCount regionCount
  generalize p.roots = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    rcases lt_trichotomy z.re 0 with hz | hz | hz
    · simp [hz, not_lt_of_gt hz, ne_of_lt hz] at *; omega
    · simp [hz] at *; omega
    · simp [hz, not_lt_of_gt hz, ne_of_gt hz] at *; omega

theorem counts_C_mul (p : ℂ[X]) (a : ℂ) (ha : a ≠ 0) :
    rightCount (C a*p) = rightCount p ∧
      axisCount (C a*p) = axisCount p := by
  simp [rightCount, axisCount, regionCount, roots_C_mul _ ha]

theorem leftCount_eq_right_neg (p : ℂ[X]) :
    leftCount p = rightCount (p.comp (-X)) := by
  simp [leftCount, rightCount, regionCount, Multiset.filter_map]

theorem leftCount_reverse (p : ℂ[X]) : leftCount p.reverse = leftCount p := by
  rw [leftCount_eq_right_neg, leftCount_eq_right_neg]
  have he : p.reverse.comp (-X) = C ((-1 : ℂ)^p.natDegree) * (p.comp (-X)).reverse := by
    ext j
    simp only [show (-X : ℂ[X]) = C (-1)*X by simp, comp_C_mul_X_coeff,
      coeff_reverse, coeff_C_mul, natDegree_comp, natDegree_C_mul (by norm_num : (-1:ℂ) ≠ 0), natDegree_X, mul_one]
    by_cases hj : j ≤ p.natDegree
    · have hh : (-1:ℂ)^p.natDegree * (-1)^(p.natDegree-j) = (-1)^j := by
        have hd : p.natDegree = (p.natDegree-j)+j := by omega
        conv_lhs => arg 1; rw [hd, pow_add]
        have hs : (-1:ℂ)^(p.natDegree-j) * (-1)^(p.natDegree-j) = 1 := by
          rw [← mul_pow]; norm_num
        linear_combination hs*((-1:ℂ)^j)
      rw [revAt_le hj]
      linear_combination -hh * (p.coeff (p.natDegree-j))
    · have hz : p.coeff (revAt p.natDegree j) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [revAt_eq_self_of_lt (by omega)]
        omega
      simp [hz]
  rw [he, (counts_C_mul _ _ (pow_ne_zero _ (by norm_num))).1, rightCount_reverse]

theorem axisCount_reverse (p : ℂ[X]) (h0 : p.coeff 0 ≠ 0) :
    axisCount p.reverse = axisCount p := by
  have hp : p ≠ 0 := by intro h; simp [h] at h0
  have hr0 : p.rootMultiplicity 0 = 0 := rootMultiplicity_eq_zero (by change p.eval 0 ≠ 0; rwa [← coeff_zero_eq_eval_zero])
  have hd : p.reverse.natDegree = p.natDegree := by
    rw [reverse, natDegree_reflect_of_le p hp _ le_rfl, hr0, Nat.sub_zero]
  have h := counts_partition p
  have hr := counts_partition p.reverse
  rw [rightCount_reverse, leftCount_reverse, hd] at hr
  omega

theorem counts_shift (p : ℂ[X]) (t : ℝ) :
    rightCount (p.comp (X+C (t*Complex.I))) = rightCount p ∧
    axisCount (p.comp (X+C (t*Complex.I))) = axisCount p := by
  have he := roots_comp_C_mul_X_add_C p 1 (t*Complex.I) isUnit_one
  simp only [map_one, one_mul] at he
  simp only [rightCount, axisCount, regionCount, he]
  simp [Multiset.filter_map]

theorem counts_axisReflect (p : ℂ[X]) : rightCount (axisReflect p) = leftCount p := by
  have hm := roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  change rightCount ((p.map (starRingEnd ℂ)).comp (-X)) = _
  simp [rightCount, leftCount, regionCount, ← hm, Multiset.filter_map]

/-- A row symmetric about the axis has equally many left and right roots. -/
theorem symmetric_counts (p : ℂ[X]) (n : ℕ) (h : Symmetric p n) :
    2*rightCount p + axisCount p = p.natDegree := by
  have he := counts_axisReflect p
  rw [h, (counts_C_mul _ _ (pow_ne_zero _ (by norm_num))).1] at he
  have := counts_partition p
  omega

theorem Symmetric.scale {u : ℂ[X]} {d : ℕ} (h : Symmetric u d) (a : ℝ) :
    Symmetric (C (a:ℂ)*u) d := by
  unfold Symmetric
  rw [map_mul, show axisReflect (C (a:ℂ)) = C (a:ℂ) by simp [axisReflect], h]
  ring

theorem Pair.count_advance {d : ℕ} {u v : ℂ[X]} (h : Pair (d+1) u v)
    (hv : (v.coeff (d+1)).re ≠ 0) :
    Pair d (C (((v.coeff (d+1)).re⁻¹ : ℝ) : ℂ)*v)
      (C (((v.coeff (d+1)).re⁻¹ : ℝ) : ℂ)*remainder d u v) := by
  refine ⟨h.lower_sym.scale _, (remainder_symmetric h).scale _,
    (natDegree_C_mul_le _ _).trans h.lower_bound,
    (natDegree_C_mul_le _ _).trans (remainder_bound h hv), ?_⟩
  simp only [coeff_C_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inv_mul_cancel₀ hv]
  norm_num

theorem Pair.eliminate_counts {d : ℕ} {u v : ℂ[X]} (h : Pair (d+1) u v)
    (hv : (v.coeff (d+1)).re ≠ 0) :
    rightCount (u+v) =
      rightCount (C (((v.coeff (d+1)).re⁻¹ : ℝ) : ℂ)*(v+remainder d u v)) +
        (if (u.coeff (d+2)).re < 0 ↔ (v.coeff (d+1)).re < 0 then 0 else 1) ∧
    axisCount (u+v) = axisCount (C (((v.coeff (d+1)).re⁻¹ : ℝ) : ℂ)*(v+remainder d u v)) := by
  have hd : v.natDegree = d+1 := natDegree_eq_of_le_of_coeff_ne_zero h.lower_bound
    (by intro hz; simp [hz] at hv)
  have hq : axisReflect v = -(C ((-1:ℂ)^(d+2))*v) := by
    rw [h.lower_sym]; simp only [pow_succ, mul_neg_one, map_neg]; ring
  have hh := reduction_counts u v ((-1)^(d+2)) (correction d u v) (ratio d u v) (d+1)
    (pow_ne_zero _ (by norm_num)) h.upper_sym hq (correction_imag h)
    (div_ne_zero (h.upper_ne) hv) (by rw [hd,h.upper_degree]; omega)
    hd ((remainder_bound h hv).trans_lt (by omega))
  have hc := counts_C_mul (v+remainder d u v) (((v.coeff (d+1)).re⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hv))
  have hs : (if ratio d u v < 0 then 1 else 0) =
      (if (u.coeff (d+2)).re < 0 ↔ (v.coeff (d+1)).re < 0 then 0 else 1) := by
    have hu := h.upper_ne
    simp only [ratio, div_neg_iff]
    rcases lt_or_gt_of_ne hu with hu | hu <;>
      rcases lt_or_gt_of_ne hv with hv | hv <;> simp [hu, hv, not_lt_of_gt hu, not_lt_of_gt hv]

  rw [hc.1, hc.2]
  simpa only [hs, remainder] using hh

theorem Pair.terminal_counts {u v : ℂ[X]} (h : Pair 0 u v)
    (hv : (v.coeff 0).re ≠ 0) :
    rightCount (u+v) = (if (u.coeff 1).re < 0 ↔ (v.coeff 0).re < 0 then 0 else 1) ∧ axisCount (u+v) = 0 := by
  let a := (u.coeff 1).re
  let b := u.coeff 0 + v.coeff 0
  have ha : a ≠ 0 := h.upper_ne
  have har : u.coeff 1 = (a:ℂ) := by
    apply Complex.ext <;> simp [a, h.upper_sym.real_coeff]
  have he : u+v = C (a:ℂ)*(X-C (-b/(a:ℂ))) := by
    rw [eq_X_add_C_of_natDegree_le_one h.upper_bound, eq_C_of_natDegree_le_zero h.lower_bound]
    rw [har]
    dsimp [b]
    simp only [mul_sub, ← map_mul]
    have hc : (a:ℂ)*(-(u.coeff 0+v.coeff 0)/(a:ℂ)) = -(u.coeff 0+v.coeff 0) := by
      field_simp [Complex.ofReal_ne_zero.mpr ha]
    rw [hc, map_neg, map_add]
    ring
  have hb : b.re = (v.coeff 0).re := by simp [b, h.upper_sym.imag_coeff]
  have hr : (-b/(a:ℂ)).re = -(v.coeff 0).re/a := by
    simp [Complex.div_ofReal_re, hb]
  have hn : (-b/(a:ℂ)).re ≠ 0 := by rw [hr]; exact div_ne_zero (neg_ne_zero.mpr hv) ha
  have hs : (if 0 < (-b/(a:ℂ)).re then 1 else 0) =
      (if (u.coeff 1).re < 0 ↔ (v.coeff 0).re < 0 then 0 else 1) := by
    rw [hr]
    change (if 0 < -(v.coeff 0).re / a then 1 else 0) =
      (if a < 0 ↔ (v.coeff 0).re < 0 then 0 else 1)
    rcases lt_or_gt_of_ne ha with ha | ha <;>
      rcases lt_or_gt_of_ne hv with hv | hv <;>
      simp [div_pos_iff, ha, hv, not_lt_of_gt ha, not_lt_of_gt hv]

  rw [he, (counts_C_mul _ _ (Complex.ofReal_ne_zero.mpr ha)).1]
  constructor
  · simpa only [rightCount_X_sub_C] using hs
  · simp [axisCount, regionCount, roots_C_mul _ (Complex.ofReal_ne_zero.mpr ha),
      roots_X_sub_C, Multiset.filter_singleton, hb, hv, ha]


/-- Independent row scalings with positive ratio preserve the represented root counts. -/
theorem pair_rescale_counts {d : ℕ} {u v : ℂ[X]} (h : ComplexRouth.Pair d u v)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b/a) :
    rightCount (C (a:ℂ)*u+C (b:ℂ)*v) = rightCount (u+v) ∧
    axisCount (C (a:ℂ)*u+C (b:ℂ)*v) = axisCount (u+v) := by
  let c : ℝ := b/a
  have hc : 0 < c := hb
  have hsym : axisReflect v = -(C ((-1:ℂ)^(d+1))*v) := by
    rw [h.lower_sym]; simp [pow_succ]
  have hu : u ≠ 0 := by intro hz; have := h.upper_degree; simp [hz] at this
  have hdeg : v.natDegree < u.natDegree := by rw [h.upper_degree]; have := h.lower_bound; omega
  have he : C (a:ℂ)*u+C (b:ℂ)*v = C (a:ℂ)*(u+C (c:ℂ)*v) := by
    have hac : (a:ℂ)*(c:ℂ) = (b:ℂ) := by dsimp [c]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr (ha)]
    rw [mul_add, ← mul_assoc, ← map_mul, hac]
  rw [he]
  have hs := counts_C_mul (u+C (c:ℂ)*v) (a:ℂ) (Complex.ofReal_ne_zero.mpr (ha))
  rw [hs.1,hs.2]
  constructor
  · apply parityMultiplier_rightCount u v (C (c:ℂ)) ((-1)^(d+1))
      (pow_ne_zero _ (by norm_num)) h.upper_sym hsym
    · simp [axisReflect]
    · intro z hz; simpa using hc
    · exact hdeg
    · exact (natDegree_C_mul_le _ _).trans_lt hdeg
  · by_cases hv : v = 0
    · simp [hv]
    · apply axisCount_eq_of_rootMultiplicity
      intro z hz
      exact parityMultiplier_axis_rootMultiplicity u v (C (c:ℂ)) ((-1)^(d+1))
        (pow_ne_zero _ (by norm_num)) h.upper_sym hsym (by simp [axisReflect]) hu hv z hz
        (by simpa using Complex.ofReal_ne_zero.mpr (ne_of_gt hc))


end
end RouthHurwitz.ComplexRouth
