import SympyProofs.ComplexRouthHurwitz.FractionFree.Basic
import SympyProofs.ComplexRouthHurwitz.Reference.Invariant

/-! Correctness of the G-sequence first elimination without conjugate scaling. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

theorem phase_ne_zero (z : ℂ) : phase z ≠ 0 := by
  unfold phase; split_ifs <;> simp

theorem phase_re_pos (z : ℂ) (hz : z ≠ 0) : 0 < (phase z*z).re := by
  have hn : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra! h; exact hz (Complex.ext h.1 h.2)
  unfold phase
  split_ifs <;> simp_all [Complex.mul_re] <;> grind

/-- Polynomial specifications of the initial rows, used only in proofs. -/
def firstLower (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  if p.leadingCoeff.im = 0 then lowerPart p n else
    C (p.leadingCoeff.re : ℂ)*lowerPart p n -
      C ((p.leadingCoeff.im : ℂ)*Complex.I)*upperPart p n

theorem parts_bound (p : ℂ[X]) (n : ℕ) (hd : p.natDegree ≤ n) :
    (upperPart p n).natDegree ≤ n ∧ (lowerPart p n).natDegree ≤ n := by
  constructor <;> apply natDegree_le_iff_coeff_eq_zero.mpr <;> intro j hj
  · rw [(parts_coeff p n j).1, coeff_eq_zero_of_natDegree_lt (hd.trans_lt hj)]
    split_ifs <;> simp
  · rw [(parts_coeff p n j).2, coeff_eq_zero_of_natDegree_lt (hd.trans_lt hj)]
    split_ifs <;> simp

theorem first_pair (p : ℂ[X]) (d : ℕ) (hd : p.natDegree=d+1)
    (ha : 0 < p.leadingCoeff.re) :
    ComplexRouth.Pair d (upperPart p (d+1)) (firstLower p (d+1)) := by
  by_cases hb : p.leadingCoeff.im = 0
  · simpa only [firstLower, hb, ite_true] using initial_pair p d hd ⟨hb,ha⟩
  have hu := upper_symmetric p (d+1)
  have hv := lower_symmetric p d
  have hbounds := parts_bound p (d+1) hd.le
  have htop := parts_coeff p (d+1) (d+1)
  simp only [ite_true, show p.coeff (d+1) = p.leadingCoeff by rw [← hd, coeff_natDegree]] at htop
  have hW : Symmetric (firstLower p (d+1)) d := by
    have hu' : axisReflect (upperPart p (d+1)) = -(C ((-1:ℂ)^d)*upperPart p (d+1)) := by
      rw [hu]; simp [pow_succ]
    simpa only [Symmetric, firstLower, hb, ite_false] using
      skew_reflect (C (p.leadingCoeff.re:ℂ)*lowerPart p (d+1)) (upperPart p (d+1))
        ((-1)^d) ((p.leadingCoeff.im:ℂ)*Complex.I) (hv.scale _) hu' (by simp)
  refine ⟨hu,hW,hbounds.1,?_,?_⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp only [firstLower, hb, ite_false, coeff_sub, coeff_C_mul]
    by_cases he : j=d+1
    · subst j; rw [htop.1, htop.2]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (hbounds.1.trans_lt (by omega)),
        coeff_eq_zero_of_natDegree_lt (hbounds.2.trans_lt (by omega))]
      simp
  · rw [htop.1]; simpa using ne_of_gt ha

theorem first_counts (p : ℂ[X]) (d : ℕ) (hd : p.natDegree=d+1)
    (ha : 0 < p.leadingCoeff.re) :
    rightCount (upperPart p (d+1)+firstLower p (d+1)) = rightCount p ∧
    axisCount (upperPart p (d+1)+firstLower p (d+1)) = axisCount p := by
  by_cases hb : p.leadingCoeff.im = 0
  · simp only [firstLower, hb, ite_true, parts_add]
    trivial
  let a := p.leadingCoeff.re
  let b := p.leadingCoeff.im
  let U := upperPart p (d+1)
  let W := firstLower p (d+1)
  let c := (a^2+b^2)/a
  let t : ℂ := (b/a : ℝ)*Complex.I
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hc : 0 < c := div_pos (by nlinarith [sq_nonneg b]) ha
  have hc0 : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hp := first_pair p d hd ha
  have hP : p ≠ 0 := by intro hz; simp [hz] at ha
  have hl : conj p.leadingCoeff ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).mpr (leadingCoeff_ne_zero.mpr hP)
  have he : (C (c:ℂ)*U-C t*W)+W = C (conj p.leadingCoeff)*p := by
    have hlc : conj p.leadingCoeff = (a:ℂ)-(b:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [a,b]
    ext j
    have hpj := congrArg (fun q : ℂ[X] => q.coeff j) (parts_add p (d+1))
    simp only [coeff_add] at hpj
    simp only [coeff_add, coeff_sub, coeff_C_mul]
    rw [hlc, ← hpj]
    dsimp only [U,W,firstLower]
    rw [ite_eq_right hb]
    simp only [coeff_sub, coeff_C_mul]
    change (c:ℂ)*(upperPart p (d+1)).coeff j - t*((a:ℂ)*(lowerPart p (d+1)).coeff j -
      (b:ℂ)*Complex.I*(upperPart p (d+1)).coeff j) +
      ((a:ℂ)*(lowerPart p (d+1)).coeff j - (b:ℂ)*Complex.I*(upperPart p (d+1)).coeff j) = _
    dsimp only [c,t]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha0]
    linear_combination (b:ℂ)^2 * (upperPart p (d+1)).coeff j * Complex.I_sq
  have hq : axisReflect W = -(C ((-1:ℂ)^(d+1))*W) := by
    rw [hp.lower_sym]; simp [pow_succ, W]
  have hu := hp.upper_sym.scale c
  have ht : conj t = -t := by simp [t]
  have hdeg : W.natDegree < (C (c:ℂ)*U).natDegree := by
    rw [natDegree_C_mul hc0, hp.upper_degree]
    exact hp.lower_bound.trans_lt (by omega)
  have hsum : C (c:ℂ)*U+W ≠ 0 := by
    intro hz
    have hh := natDegree_add_eq_left_of_natDegree_lt hdeg
    rw [hz, natDegree_zero, natDegree_C_mul hc0, hp.upper_degree] at hh
    omega
  have hnew : (C (c:ℂ)*U-C t*W)+W ≠ 0 := by
    rw [he]; exact mul_ne_zero (C_ne_zero.mpr hl) hP
  have hs := pair_rescale_counts hp c 1 (ne_of_gt hc) (by simpa using one_div_pos.mpr hc)
  simp only [Complex.ofReal_one, map_one, one_mul] at hs
  have hr := skew_rightCount (C (c:ℂ)*U) W ((-1)^(d+1)) t
    (pow_ne_zero _ (by norm_num)) hu hq ht hdeg
  have haxis := axisCount_eq_of_rootMultiplicity _ _ (fun z hz =>
    skew_axis (C (c:ℂ)*U) W ((-1)^(d+1)) t (pow_ne_zero _ (by norm_num)) hu hq ht hsum hnew z hz)
  rw [he, (counts_C_mul p _ hl).1] at hr
  rw [he, (counts_C_mul p _ hl).2] at haxis
  exact ⟨hs.1.symm.trans hr.symm, hs.2.symm.trans haxis.symm⟩

theorem initialRows_pack {N} (p : ℂ[X]) (n : ℕ) (hd : p.natDegree=n) (hN : n<N) :
    initialRows (Coefficients.pack N p) n =
      ⟨Coefficients.pack N (upperPart p n), Coefficients.pack N (firstLower p n)⟩ := by
  simp only [initialRows, Coefficients.scan_pack, ComplexRouth.scan,
    Coefficients.entry_pack p (hd ▸ hN), ← hd, coeff_natDegree]
  congr 1
  by_cases hb : p.leadingCoeff.im=0
  · simp [firstLower,hb]
  · simp only [hb, ite_false, firstLower]
    apply Vector.ext; intro j hj
    simp [Coefficients.pack, coeff_sub, coeff_C_mul]
    rw [← map_mul, coeff_C_mul]

theorem initialDivisor_pack {N} (p : ℂ[X]) (n : ℕ) (hd : p.natDegree=n) (hN : n<N) :
    initialDivisor (Coefficients.pack N p) n =
      if p.leadingCoeff.im=0 then 1 else p.leadingCoeff.re := by
  simp only [initialDivisor, Coefficients.entry_pack p (hd ▸ hN), ← hd, coeff_natDegree]

end
end RouthHurwitz.ComplexRouth.FractionFree
