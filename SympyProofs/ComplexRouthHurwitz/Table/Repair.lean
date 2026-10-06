import SympyProofs.ComplexRouthHurwitz.Table.Counts

/-! Correctness of reciprocal and derivative repairs for complex rows. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

theorem wronskian_ne_zero_of_degree_lt (u v : ℂ[X]) (hv : v ≠ 0)
    (hd : v.natDegree < u.natDegree) : wronskian u v ≠ 0 := by
  have hu : u ≠ 0 := by intro hz; simp [hz] at hd
  intro hz
  have he : u*v.derivative = u.derivative*v := sub_eq_zero.mp hz
  have hl := congrArg Polynomial.leadingCoeff he
  rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_derivative,
    leadingCoeff_derivative] at hl
  have hh : (u.leadingCoeff*v.leadingCoeff)*
      ((v.natDegree : ℂ)-(u.natDegree : ℂ)) = 0 := by linear_combination hl
  have hc := (mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hu) (leadingCoeff_ne_zero.mpr hv))
  have hn : v.natDegree = u.natDegree := by exact_mod_cast sub_eq_zero.mp hc
  omega

theorem eval_axisReflect (p : ℂ[X]) (z : ℂ) (hz : z.re = 0) :
    (axisReflect p).eval z = conj (p.eval z) := by
  have he : -z = conj z := by apply Complex.ext <;> simp [hz]
  change ((p.map (starRingEnd ℂ)).comp (-X)).eval z = _
  rw [eval_comp]
  simp only [eval_neg, eval_X, he]
  exact eval_map_apply _ _

/-- A nonzero Wronskian value supplies a nonzero reciprocal pivot. -/
theorem reciprocal_pivot_ne_zero (u v : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hu : axisReflect u = C σ*u) (hv : axisReflect v = -(C σ*v))
    (z : ℂ) (hz : z.re = 0) (hw : (wronskian u v).eval z ≠ 0) :
    (u+v).eval z ≠ 0 ∧ ((u+v).derivative.eval z / (u+v).eval z).re ≠ 0 := by
  let p := u+v
  have hp : axisReflect p = C σ*(u-v) := by simp only [p, map_add, hu, hv]; ring
  have hc : conj (p.eval z) = σ*(u.eval z-v.eval z) := by
    rw [← eval_axisReflect p z hz, hp, eval_mul, eval_C, eval_sub]
  have hdc : conj (p.derivative.eval z) = -σ*(u.derivative.eval z-v.derivative.eval z) := by
    rw [← eval_axisReflect p.derivative z hz, axisReflect_derivative, hp,
      derivative_C_mul, derivative_sub, eval_neg, eval_mul, eval_C, eval_sub]
    ring
  have he : p.derivative.eval z * conj (p.eval z) +
      conj (p.derivative.eval z)*p.eval z = 2*σ*(wronskian u v).eval z := by
    rw [hc, hdc]
    simp only [p, derivative_add, eval_add, wronskian, eval_sub, eval_mul]
    ring
  have hne : 2*σ*(wronskian u v).eval z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hσ) hw
  have hp0 : p.eval z ≠ 0 := by
    intro hh
    simp only [hh, map_zero, mul_zero, zero_add] at he
    exact hne he.symm
  refine ⟨hp0, ?_⟩
  intro hh
  have hnorm : Complex.normSq (p.eval z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hp0)
  have hre : (p.derivative.eval z).re*(p.eval z).re +
      (p.derivative.eval z).im*(p.eval z).im = 0 := by
    rw [Complex.div_re, ← add_div] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right hnorm
  apply hne
  rw [← he]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im]
  · linear_combination 2*hre
  · ring

theorem repairOffset_spec (d : ℕ) (u v : ℂ[X]) (hv : v ≠ 0)
    (hd : v.natDegree < u.natDegree) (hu : u.natDegree ≤ d+1) :
    (wronskian u v).eval ((repairOffset d u v : ℂ)*Complex.I) ≠ 0 := by
  let w := wronskian u v
  have hw : w ≠ 0 := wronskian_ne_zero_of_degree_lt u v hv hd
  have hex : ∃ j ∈ List.range (2*(d+1)+1), w.eval ((j:ℂ)*Complex.I) ≠ 0 := by
    by_contra! he
    apply hw
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero w
      (f := fun j : Fin (2*(d+1)+1) => (j.val:ℂ)*Complex.I)
    · intro i j hij
      apply Fin.ext
      have hc := mul_right_cancel₀ Complex.I_ne_zero hij
      exact_mod_cast hc
    · intro j
      exact he j.val (by simpa using j.isLt)
    · have hb := natDegree_wronskian_lt_add hw
      simp only [Fintype.card_fin]
      dsimp [w]
      omega
  unfold repairOffset
  change w.eval ((((List.find? _ _).getD 0 : ℕ) : ℂ)*Complex.I) ≠ 0
  cases he : (List.range (2*(d+1)+1)).find?
      (fun j : ℕ => decide (w.eval ((j:ℂ)*Complex.I) ≠ 0)) with
  | none =>
    obtain ⟨j,hj,hv⟩ := hex
    have hh := List.find?_eq_none.mp he j hj
    simp [hv] at hh
  | some j =>
    simpa using List.find?_some he

theorem reciprocal_spec (p : ℂ[X]) (t : ℝ) (h0 : p.eval (t*Complex.I) ≠ 0)
    (hn : 0 < p.natDegree) :
    PositiveLeading (reciprocal p t) ∧ (reciprocal p t).natDegree = p.natDegree ∧
    (reciprocal p t).nextCoeff / (reciprocal p t).leadingCoeff = p.derivative.eval (t*Complex.I) / p.eval (t*Complex.I) ∧
    rightCount (reciprocal p t) = rightCount p ∧
    axisCount (reciprocal p t) = axisCount p := by
  let a := taylor (t*Complex.I) p
  have ha0 : a.coeff 0 ≠ 0 := by simpa [a, taylor_coeff_zero] using h0
  have ha : a ≠ 0 := by intro hz; simp [hz] at ha0
  have hr : a.reverse ≠ 0 := reverse_eq_zero.not.mpr ha
  have hmul : (conj a.reverse.leadingCoeff) ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).mpr (leadingCoeff_ne_zero.mpr hr)
  have hroot : a.rootMultiplicity 0 = 0 := rootMultiplicity_eq_zero (by
    change a.eval 0 ≠ 0
    rwa [← coeff_zero_eq_eval_zero])
  have hd : a.reverse.natDegree = p.natDegree := by
    rw [reverse, natDegree_reflect_of_le a ha _ le_rfl, hroot, Nat.sub_zero]
    exact natDegree_taylor _ _
  have hl : a.reverse.leadingCoeff = p.eval (t*Complex.I) := by
    rw [leadingCoeff, hd, coeff_reverse, show a.natDegree = p.natDegree from natDegree_taylor _ _,
      revAt_le le_rfl, Nat.sub_self]
    exact taylor_coeff_zero _ _
  have hc : a.reverse.nextCoeff = p.derivative.eval (t*Complex.I) := by
    rw [nextCoeff, hd, ite_eq_right (by omega), coeff_reverse,
      show a.natDegree = p.natDegree from natDegree_taylor _ _, revAt_le (by omega),
      show p.natDegree-(p.natDegree-1)=1 by omega]
    exact taylor_coeff_one _ _
  have hs := counts_shift p t
  change rightCount a = rightCount p ∧ axisCount a = axisCount p at hs
  have hscale := counts_C_mul a.reverse (conj a.reverse.leadingCoeff) hmul
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PositiveLeading, reciprocal, leadingCoeff_mul, leadingCoeff_C, Complex.mul_conj,
      Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨by simp, Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hr)⟩
  · exact (natDegree_mul_C hmul).trans hd
  · change (a.reverse * C (conj a.reverse.leadingCoeff)).nextCoeff /
      (a.reverse * C (conj a.reverse.leadingCoeff)).leadingCoeff = _
    rw [nextCoeff_mul_C, leadingCoeff_mul, leadingCoeff_C, hl, hc]
    exact mul_div_mul_right _ _ ((_root_.map_ne_zero (starRingEnd ℂ)).mpr h0)
  · change rightCount (a.reverse * C (conj a.reverse.leadingCoeff)) = _
    rw [mul_comm, hscale.1, rightCount_reverse, hs.1]
  · change axisCount (a.reverse * C (conj a.reverse.leadingCoeff)) = _
    rw [mul_comm, hscale.2, axisCount_reverse a ha0, hs.2]

theorem Pair.derivative_pair {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) :
    Pair d u u.derivative ∧ (u.derivative.coeff d).re ≠ 0 := by
  have hp : (u.derivative.coeff d).re ≠ 0 := by
    simp [coeff_derivative, Complex.mul_re]
    exact ⟨h.upper_ne, ne_of_gt (by positivity)⟩
  refine ⟨⟨h.upper_sym, ?_, h.upper_bound, ?_, h.upper_ne⟩, hp⟩
  · unfold Symmetric
    rw [axisReflect_derivative, h.upper_sym, derivative_C_mul]
    simp only [pow_succ, mul_neg_one, map_neg]
    ring
  · rw [natDegree_derivative, h.upper_degree]
    omega

/-- The selected shift gives a nonzero value and a usable reciprocal pivot. -/
theorem Pair.repairOffset_valid {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) (hv : v ≠ 0) :
    let z : ℂ := (repairOffset d u v : ℝ)*Complex.I
    (u+v).eval z ≠ 0 ∧ ((u+v).derivative.eval z / (u+v).eval z).re ≠ 0 := by
  let t : ℝ := repairOffset d u v
  have hq : axisReflect v = -(C ((-1:ℂ)^(d+1))*v) := by
    rw [h.lower_sym]; simp [pow_succ]
  have hw := repairOffset_spec d u v hv (by rw [h.upper_degree]; exact h.lower_bound.trans_lt (by omega)) h.upper_bound
  exact reciprocal_pivot_ne_zero u v ((-1)^(d+1)) (pow_ne_zero _ (by norm_num))
    h.upper_sym hq (t*Complex.I) (by simp) (by simpa [t] using hw)

theorem Pair.reciprocal_pair {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) (hv : v ≠ 0) :
    let r := scan (reciprocal (u+v) (repairOffset d u v)) (d+1)
    Pair d r.upper r.lower ∧ (r.lower.coeff d).re ≠ 0 ∧
      rightCount (r.upper+r.lower) = rightCount (u+v) ∧
      axisCount (r.upper+r.lower) = axisCount (u+v) := by
  let t : ℝ := repairOffset d u v
  have hp := h.repairOffset_valid hv
  have hs := reciprocal_spec (u+v) t hp.1 (by rw [h.sum_degree]; omega)
  let q := reciprocal (u+v) t
  have hd : q.natDegree = d+1 := hs.2.1.trans h.sum_degree
  have hi := initial_pair q d hd hs.1
  change let r := scan q (d+1); _
  rw [scan]
  dsimp only
  refine ⟨hi, ?_, ?_, ?_⟩
  · have hc : q.nextCoeff.re = ((lowerPart q (d+1)).coeff d).re := by
      rw [nextCoeff, hd, ite_eq_right (by omega), Nat.add_sub_cancel]
      have he := congrArg (fun a : ℂ[X] => (a.coeff d).re) (parts_add q (d+1))
      simpa only [coeff_add, Complex.add_re, hi.upper_sym.imag_coeff, zero_add] using he.symm
    intro hz
    apply hp.2
    rw [← hs.2.2.1]
    have hlc : q.leadingCoeff = (q.leadingCoeff.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hs.1.1
    rw [hlc, Complex.div_ofReal_re, hc, hz, zero_div]
  · rw [parts_add]; exact hs.2.2.2.1
  · rw [parts_add]; exact hs.2.2.2.2

/-- Repairs always produce a usable pivot and preserve the right count.
Until a zero row occurs, they also preserve the entire axis count. -/
theorem Pair.repair_correct {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) :
    let r := repair d u v
    Pair d r.upper r.lower ∧ (r.lower.coeff d).re ≠ 0 ∧
      rightCount (r.upper+r.lower) = rightCount (u+v) ∧
      (v ≠ 0 → axisCount (r.upper+r.lower) = axisCount (u+v)) := by
  unfold repair
  split_ifs with hv hp
  · have hi := h.derivative_pair
    refine ⟨hi.1, hi.2, ?_, fun hh => (hh hv).elim⟩
    rw [hv, add_zero]
    exact derivativeRepair_rightCount u ((-1)^(d+1)) (pow_ne_zero _ (by norm_num))
      h.upper_sym (by rw [h.upper_degree]; omega)
  · have hi := h.reciprocal_pair hv
    exact ⟨hi.1, hi.2.1, hi.2.2.1, fun _ => hi.2.2.2⟩
  · exact ⟨h, hp, rfl, fun _ => rfl⟩


end
end RouthHurwitz.ComplexRouth
