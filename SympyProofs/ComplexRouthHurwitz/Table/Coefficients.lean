import SympyProofs.ComplexRouthHurwitz.Table.Repair

/-! Refinement of coordinate arithmetic by the polynomial specifications. -/
namespace RouthHurwitz.ComplexRouth.Coefficients
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

def pack (N : ℕ) (p : ℂ[X]) : Row N := Vector.ofFn (fun j => p.coeff j.val)

@[simp] theorem pack_get (N : ℕ) (p : ℂ[X]) (j : ℕ) (hj : j < N) :
    (pack N p)[j] = p.coeff j := by simp [pack]

@[simp] theorem entry_pack {N : ℕ} (p : ℂ[X]) (hp : p.natDegree < N) (j : ℕ) :
    entry (pack N p) j = p.coeff j := by
  by_cases hj : j < N
  · simp [entry, hj]
  · simp [entry, hj, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]

@[simp] theorem pack_zero (N : ℕ) : pack N 0 = zero N := by
  apply Vector.ext; intro j hj; simp [pack, zero]
@[simp] theorem pack_one (N : ℕ) : pack N 1 = one N := by
  apply Vector.ext; intro j hj; simp [pack, one, coeff_one]

theorem pack_eq_zero {N : ℕ} (p : ℂ[X]) (hp : p.natDegree < N) :
    pack N p = zero N ↔ p = 0 := by
  constructor
  · intro h
    ext j
    have he := entry_pack p hp j
    rw [h] at he
    simpa [entry, zero] using he.symm
  · rintro rfl; exact pack_zero N

@[simp] theorem add_pack (N : ℕ) (p q : ℂ[X]) :
    add (pack N p) (pack N q) = pack N (p+q) := by
  apply Vector.ext; intro j hj; simp [add, pack]
@[simp] theorem scale_pack (N : ℕ) (c : ℂ) (p : ℂ[X]) :
    scale c (pack N p) = pack N (C c*p) := by
  apply Vector.ext; intro j hj; simp [scale, pack]

theorem derivative_pack {N : ℕ} (p : ℂ[X]) (hp : p.natDegree < N) :
    derivative (pack N p) = pack N p.derivative := by
  apply Vector.ext; intro j hj
  simp [derivative, entry_pack p hp, coeff_derivative]

theorem eval_pack {N : ℕ} (p : ℂ[X]) (hp : p.natDegree < N) (z : ℂ) :
    eval (pack N p) z = p.eval z := by
  simp only [eval, Fin.getElem_fin, pack, Vector.getElem_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun j => p.coeff j*z^j) N, eval_eq_sum_range' hp]

theorem scan_pack {N : ℕ} (p : ℂ[X]) (n : ℕ) :
    scan (pack N p) n =
      ⟨pack N (ComplexRouth.scan p n).upper, pack N (ComplexRouth.scan p n).lower⟩ := by
  rw [ComplexRouth.scan]
  unfold scan
  congr 1 <;> apply Vector.ext <;> intro j hj
  · simpa [scan, pack] using (parts_coeff p n j).1.symm
  · simpa [scan, pack] using (parts_coeff p n j).2.symm

theorem remainder_pack {N : ℕ} (d : ℕ) (u v : ℂ[X])
    (hu : u.natDegree < N) (hv : v.natDegree < N) :
    remainder d (pack N u) (pack N v) = pack N (ComplexRouth.remainder d u v) := by
  apply Vector.ext; intro j hj
  cases j with
  | zero => simp [remainder, ComplexRouth.remainder, ratio, correction, entry_pack u hu,
      entry_pack v hv, mul_assoc]
  | succ j => simp [remainder, ComplexRouth.remainder, ratio, correction, entry_pack u hu,
      entry_pack v hv, mul_assoc, coeff_X_mul]

theorem repairOffset_pack {N : ℕ} (d : ℕ) (u v : ℂ[X])
    (hu : u.natDegree < N) (hv : v.natDegree < N) :
    repairOffset d (pack N u) (pack N v) = ComplexRouth.repairOffset d u v := by
  have hdu : u.derivative.natDegree < N := (natDegree_derivative_le u).trans_lt (by omega)
  have hdv : v.derivative.natDegree < N := (natDegree_derivative_le v).trans_lt (by omega)
  simp only [repairOffset, ComplexRouth.repairOffset, derivative_pack u hu, derivative_pack v hv,
    eval_pack u hu, eval_pack v hv, eval_pack _ hdu, eval_pack _ hdv,
    wronskian, eval_sub, eval_mul]

theorem shift_coeff {N : ℕ} (p : ℂ[X]) (hp : p.natDegree < N) (z : ℂ) (k : ℕ) :
    (taylor z p).coeff k = ∑ j : Fin N, p.coeff j.val * (j.val.choose k : ℂ) * z^(j.val-k) := by
  rw [taylor_coeff]
  conv_lhs => rw [p.as_sum_range' N hp]
  simp only [map_sum, hasseDeriv_monomial, eval_finsetSum, eval_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun j => p.coeff j*(j.choose k : ℂ)*z^(j-k)) N]
  apply Finset.sum_congr rfl; intro j hj; ring

theorem reciprocal_pack {N : ℕ} (p : ℂ[X]) (m : ℕ) (t : ℝ)
    (hd : p.natDegree = m) (hm : m < N) (h0 : p.eval (t*Complex.I) ≠ 0) :
    reciprocal (pack N p) m t = pack N (ComplexRouth.reciprocal p t) := by
  let a := taylor (t*Complex.I) p
  have ha : a.natDegree = m := (natDegree_taylor _ _).trans hd
  have ha0 : a.coeff 0 ≠ 0 := by simpa [a] using h0
  have har : a.reverse.natDegree = m := by
    have hane : a ≠ 0 := by intro h; simp [h] at ha0
    have hz : a.rootMultiplicity 0 = 0 := rootMultiplicity_eq_zero (by
      change a.eval 0 ≠ 0
      rwa [← coeff_zero_eq_eval_zero])
    rw [reverse, natDegree_reflect_of_le a hane _ le_rfl, hz, Nat.sub_zero, ha]
  have hl : a.reverse.leadingCoeff = p.eval (t*Complex.I) := by
    rw [leadingCoeff, har, coeff_reverse, ha, revAt_le le_rfl, Nat.sub_self]
    exact taylor_coeff_zero _ _
  have hp : p.natDegree < N := by omega
  apply Vector.ext; intro j hj
  simp only [reciprocal, Vector.getElem_ofFn, pack_get, eval_pack p hp, Fin.getElem_fin,
    ComplexRouth.reciprocal, coeff_mul_C]
  change (if j ≤ m then _ else 0) = a.reverse.coeff j * conj a.reverse.leadingCoeff
  rw [hl]
  by_cases hjm : j ≤ m
  · rw [ite_eq_left hjm, ← shift_coeff p hp, coeff_reverse, ha, revAt_le hjm]
  · rw [ite_eq_right hjm, coeff_eq_zero_of_natDegree_lt (by omega : a.reverse.natDegree < j)]
    simp

theorem repair_pack {N : ℕ} (d : ℕ) (u v : ℂ[X])
    (h : ComplexRouth.Pair d u v) (hN : d+1 < N) :
    repair d (pack N u) (pack N v) =
      ⟨pack N (ComplexRouth.repair d u v).upper,
        pack N (ComplexRouth.repair d u v).lower⟩ := by
  have hu : u.natDegree < N := h.upper_bound.trans_lt hN
  have hv : v.natDegree < N := h.lower_bound.trans_lt (by omega)
  simp only [repair, ComplexRouth.repair, pack_eq_zero v hv, entry_pack v hv]
  by_cases hz : v = 0
  · simp [hz, derivative_pack u hu]
  · simp only [hz, ite_false]
    by_cases hp : (v.coeff d).re = 0
    · simp only [hp, ite_true, add_pack, repairOffset_pack d u v hu hv]
      let t : ℝ := ComplexRouth.repairOffset d u v
      have he := h.repairOffset_valid hz
      rw [reciprocal_pack (u+v) (d+1) t h.sum_degree hN he.1]
      exact scan_pack _ _
    · simp [hp]

end
end RouthHurwitz.ComplexRouth.Coefficients
