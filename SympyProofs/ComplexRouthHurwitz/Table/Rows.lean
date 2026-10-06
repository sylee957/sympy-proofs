import SympyProofs.ComplexRouthHurwitz.Table.Model

namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate

private theorem sign_sq (n : ℕ) : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by
  rw [← mul_pow]; norm_num

@[simp] theorem reflect_coeff (p : ℂ[X]) (j : ℕ) :
    (axisReflect p).coeff j = conj (p.coeff j) * (-1)^j := by
  change ((p.map (starRingEnd ℂ)).comp (-X)).coeff j = _
  rw [show (-X : ℂ[X]) = C (-1)*X by simp, comp_C_mul_X_coeff, coeff_map]

@[simp] theorem reflect_reflect (p : ℂ[X]) : axisReflect (axisReflect p) = p := by
  ext j
  simp only [reflect_coeff, map_mul, map_pow, map_neg, map_one, starRingEnd_self_apply]
  rw [mul_assoc, sign_sq, mul_one]

/-- Alternating real/imaginary row symmetry. -/
def Symmetric (p : ℂ[X]) (d : ℕ) : Prop := axisReflect p = C ((-1)^d) * p

theorem Symmetric.real_coeff {p : ℂ[X]} {d : ℕ} (h : Symmetric p d) :
    (p.coeff d).im = 0 := by
  have he := congrArg (fun q : ℂ[X] => q.coeff d) h
  simp only [reflect_coeff, coeff_C_mul] at he
  have hc : conj (p.coeff d) = p.coeff d :=
    (mul_right_cancel₀ (pow_ne_zero d (by norm_num : (-1 : ℂ) ≠ 0))) (by simpa [mul_comm] using he)
  have := congrArg Complex.im hc
  simp only [Complex.conj_im] at this
  linarith

theorem Symmetric.imag_coeff {p : ℂ[X]} {d : ℕ} (h : Symmetric p (d+1)) :
    (p.coeff d).re = 0 := by
  have he := congrArg (fun q : ℂ[X] => q.coeff d) h
  simp only [reflect_coeff, coeff_C_mul, pow_succ] at he
  have hc : conj (p.coeff d) = -(p.coeff d) :=
    (mul_right_cancel₀ (pow_ne_zero d (by norm_num : (-1 : ℂ) ≠ 0))) (by linear_combination he)
  have := congrArg Complex.re hc
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem parts_add (p : ℂ[X]) (n : ℕ) : upperPart p n + lowerPart p n = p := by
  unfold upperPart lowerPart
  have h := congrArg (C : ℂ → ℂ[X]) (show (1/2 : ℂ)+(1/2)=1 by norm_num)
  simp only [map_add, map_one] at h
  linear_combination h*p

theorem upper_symmetric (p : ℂ[X]) (n : ℕ) : Symmetric (upperPart p n) n := by
  have hs : C ((-1 : ℂ)^n) * C ((-1 : ℂ)^n) = (1 : ℂ[X]) := by rw [← map_mul, sign_sq, map_one]
  have hc : axisReflect (C (1/2 : ℂ)) = C (1/2 : ℂ) := by simp [axisReflect, map_ofNat]
  have hc' : axisReflect (C ((-1 : ℂ)^n)) = C ((-1 : ℂ)^n) := by simp [axisReflect]
  unfold Symmetric upperPart
  rw [map_mul, map_add, map_mul, hc, hc', reflect_reflect]
  linear_combination -C (1/2 : ℂ)*hs*(axisReflect p)

theorem lower_symmetric (p : ℂ[X]) (n : ℕ) : Symmetric (lowerPart p (n+1)) n := by
  have hs : C ((-1 : ℂ)^n) * C ((-1 : ℂ)^n) = (1 : ℂ[X]) := by rw [← map_mul, sign_sq, map_one]
  have hc : axisReflect (C (1/2 : ℂ)) = C (1/2 : ℂ) := by simp [axisReflect, map_ofNat]
  have hc' : axisReflect (C ((-1 : ℂ)^(n+1))) = C ((-1 : ℂ)^(n+1)) := by simp [axisReflect]
  unfold Symmetric lowerPart
  rw [map_mul, map_sub, map_mul, hc, hc', reflect_reflect]
  simp only [pow_succ, mul_neg_one, map_neg]
  linear_combination -C (1/2 : ℂ)*hs*(axisReflect p)

/-- Invariant of a current pair at remaining lower-row degree d. -/
structure Pair (d : ℕ) (u v : ℂ[X]) : Prop where
  upper_sym : Symmetric u (d+1)
  lower_sym : Symmetric v d
  upper_bound : u.natDegree ≤ d+1
  lower_bound : v.natDegree ≤ d
  upper_ne : (u.coeff (d+1)).re ≠ 0

theorem Pair.upper_degree {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) : u.natDegree = d+1 :=
  natDegree_eq_of_le_of_coeff_ne_zero h.upper_bound (by
    intro hz; have := h.upper_ne; simp [hz] at this)

theorem Pair.sum_degree {d : ℕ} {u v : ℂ[X]} (h : Pair d u v) : (u+v).natDegree = d+1 := by
  rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h.upper_degree]; have := h.lower_bound; omega), h.upper_degree]

private theorem coeff_eq_real (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

theorem correction_imag {d : ℕ} {u v : ℂ[X]} (h : Pair (d+1) u v) :
    conj (correction d u v) = -correction d u v := by
  have hu : conj (u.coeff (d+1)) = -u.coeff (d+1) := by
    apply Complex.ext <;> simp [h.upper_sym.imag_coeff]
  have hv : conj (v.coeff d) = -v.coeff d := by
    apply Complex.ext <;> simp [h.lower_sym.imag_coeff]
  have hv' : conj (v.coeff (d+1)) = v.coeff (d+1) := by
    apply Complex.ext <;> simp [h.lower_sym.real_coeff]
  simp only [correction, map_div₀, map_sub, map_mul, hu, hv, hv', Complex.conj_ofReal]
  ring

theorem remainder_bound {d : ℕ} {u v : ℂ[X]} (h : Pair (d+1) u v)
    (hv : (v.coeff (d+1)).re ≠ 0) : (remainder d u v).natDegree ≤ d := by
  have hv0 : v.coeff (d+1) ≠ 0 := by intro he; simp [he] at hv
  have hur := coeff_eq_real _ h.upper_sym.real_coeff
  have hvr := coeff_eq_real _ h.lower_sym.real_coeff
  have hlead : (ratio d u v : ℂ) * v.coeff (d+1) = u.coeff (d+2) := by
    rw [hur, hvr]
    push_cast [ratio]
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hv)]
  have hnext : correction d u v * v.coeff (d+1) =
      u.coeff (d+1) - (ratio d u v : ℂ) * v.coeff d :=
    div_mul_cancel₀ _ hv0
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have jpos : 0 < j := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have he : C (ratio d u v : ℂ)*X*v = C (ratio d u v : ℂ)*(v*X) := by ring
  simp only [remainder, he, coeff_sub, coeff_C_mul, coeff_mul_X]
  by_cases hk : k = d
  · subst k
    linear_combination -hnext
  · by_cases hk' : k = d+1
    · subst k
      have hz : v.coeff (d+1+1) = 0 := coeff_eq_zero_of_natDegree_lt (by have := h.lower_bound; omega)
      simp only [hz, mul_zero, sub_zero]
      exact sub_eq_zero.mpr hlead.symm
    · have hu0 : u.coeff (k+1) = 0 := coeff_eq_zero_of_natDegree_lt (by have := h.upper_bound; omega)
      have hv1 : v.coeff (k+1) = 0 := coeff_eq_zero_of_natDegree_lt (by have := h.lower_bound; omega)
      have hv2 : v.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by have := h.lower_bound; omega)
      simp [hu0,hv1,hv2]

theorem remainder_symmetric {d : ℕ} {u v : ℂ[X]} (h : Pair (d+1) u v) :
    Symmetric (remainder d u v) d := by
  have hb := correction_imag h
  have hc : axisReflect (C (ratio d u v : ℂ)) = C (ratio d u v : ℂ) := by simp [axisReflect]
  have hcb : axisReflect (C (correction d u v)) = -C (correction d u v) := by
    simp [axisReflect, hb]
  have hx : axisReflect (X : ℂ[X]) = -X := by simp [axisReflect]
  unfold Symmetric remainder
  rw [map_sub, map_sub, map_mul, map_mul, map_mul, h.upper_sym, h.lower_sym, hc, hcb, hx]
  simp only [pow_succ, mul_neg_one, map_neg]
  ring

theorem initial_pair (p : ℂ[X]) (n : ℕ) (hd : p.natDegree = n+1) (hp : PositiveLeading p) :
    Pair n (upperPart p (n+1)) (lowerPart p (n+1)) := by
  have hcoeff : p.coeff (n+1) = p.leadingCoeff := by rw [← hd, coeff_natDegree]
  have hc : conj p.leadingCoeff = p.leadingCoeff := Complex.conj_eq_iff_im.mpr hp.1
  have hu : (upperPart p (n+1)).coeff (n+1) = p.leadingCoeff := by
    simp only [upperPart, coeff_C_mul, coeff_add, reflect_coeff, hcoeff, hc]
    have hs := sign_sq (n+1)
    linear_combination p.leadingCoeff*hs/2
  have hl : (lowerPart p (n+1)).coeff (n+1) = 0 := by
    simp only [lowerPart, coeff_C_mul, coeff_sub, reflect_coeff, hcoeff, hc]
    have hs := sign_sq (n+1)
    linear_combination -p.leadingCoeff*hs/2
  have hub : (upperPart p (n+1)).natDegree ≤ n+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    have hz : p.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [upperPart, coeff_C_mul, coeff_add, reflect_coeff, hz, map_zero, zero_mul, mul_zero, add_zero]
  have hlb : (lowerPart p (n+1)).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_cases he : j = n+1
    · simpa [he] using hl
    · have hz : p.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [lowerPart, coeff_C_mul, coeff_sub, reflect_coeff, hz, map_zero, zero_mul, mul_zero, sub_zero]
  exact ⟨upper_symmetric p _, lower_symmetric p n, hub, hlb, by rw [hu]; exact ne_of_gt hp.2⟩

noncomputable section
open Classical

theorem parts_coeff (p : ℂ[X]) (n j : ℕ) :
    (upperPart p n).coeff j =
      (if n % 2 = j % 2 then (p.coeff j).re else (p.coeff j).im * Complex.I : ℂ) ∧
    (lowerPart p n).coeff j =
      (if n % 2 = j % 2 then (p.coeff j).im * Complex.I else (p.coeff j).re : ℂ) := by
  simp only [upperPart, lowerPart, coeff_C_mul, coeff_add, coeff_sub, reflect_coeff]
  rw [neg_one_pow_eq_pow_mod_two n, neg_one_pow_eq_pow_mod_two j]
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  have hj := Nat.mod_lt j (by decide : 0 < 2)
  interval_cases hn' : n % 2 <;> interval_cases hj' : j % 2 <;>
    simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;> ring_nf <;> simp

end
end RouthHurwitz.ComplexRouth
