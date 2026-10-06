import SympyProofs.RouthHurwitz.Table.Stability

/-! Direct complex Routh reduction: an imaginary constant correction followed
by the real leading-term elimination. No conjugate-product polynomial is used. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate

theorem skew_reflect (P Q : ℂ[X]) (σ b : ℂ)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (hb : conj b = -b) :
    axisReflect (P - C b * Q) = C σ * (P - C b * Q) := by
  rw [map_sub, map_mul, hP, hQ]
  have hc : axisReflect (C b) = C (conj b) := by simp [axisReflect]
  rw [hc, hb, map_neg]
  ring

private theorem skew_axis_dvd (P Q : ℂ[X]) (σ b : ℂ) (hσ : σ ≠ 0)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (hb : conj b = -b) (z : ℂ) (hz : z.re = 0) (m : ℕ) :
    (X-C z)^m ∣ (P-C b*Q)+Q ↔ (X-C z)^m ∣ P+Q := by
  rw [axis_power_dvd_add_iff _ Q σ hσ (skew_reflect P Q σ b hP hQ hb) hQ z hz m,
    axis_power_dvd_add_iff P Q σ hσ hP hQ z hz m]
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨by simpa using dvd_add h (dvd_mul_of_dvd_right hq (C b)), hq⟩
  · rintro ⟨h, hq⟩
    exact ⟨dvd_sub h (dvd_mul_of_dvd_right hq (C b)), hq⟩

theorem skew_axis (P Q : ℂ[X]) (σ b : ℂ) (hσ : σ ≠ 0)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (hb : conj b = -b) (hs : P+Q ≠ 0) (ht : (P-C b*Q)+Q ≠ 0)
    (z : ℂ) (hz : z.re = 0) :
    ((P-C b*Q)+Q).rootMultiplicity z = (P+Q).rootMultiplicity z := by
  apply Nat.le_antisymm
  · exact (le_rootMultiplicity_iff hs).mpr
      ((skew_axis_dvd P Q σ b hσ hP hQ hb z hz _).mp (pow_rootMultiplicity_dvd _ z))
  · exact (le_rootMultiplicity_iff ht).mpr
      ((skew_axis_dvd P Q σ b hσ hP hQ hb z hz _).mpr (pow_rootMultiplicity_dvd _ z))

/-- Removing an imaginary multiple of the lower row preserves the RHP count. -/
theorem skew_rightCount (P Q : ℂ[X]) (σ b : ℂ) (hσ : σ ≠ 0)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (hb : conj b = -b) (hdeg : Q.natDegree < P.natDegree) :
    rightCount ((P-C b*Q)+Q) = rightCount (P+Q) := by
  let A := P+Q
  let B := -(C b*Q)
  have hd : A.natDegree = P.natDegree := natDegree_add_eq_left_of_natDegree_lt hdeg
  have hbdeg : B.natDegree < A.natDegree := by
    dsimp [B]
    rw [natDegree_neg, hd]
    exact (natDegree_C_mul_le _ _).trans_lt hdeg
  have hdn (t : ℂ) := natDegree_affine_of_lt A B hbdeg t
  have hp (t : unitInterval) : A+C (t : ℂ)*B ≠ 0 := by
    intro hz
    have hh := hdn (t : ℂ)
    rw [hz, natDegree_zero, hd] at hh
    omega
  have hA : A ≠ 0 := by simpa using hp 0
  have ha (t : unitInterval) (z : ℂ) (hz : z.re = 0) :
      (A+C (t : ℂ)*B).rootMultiplicity z = A.rootMultiplicity z := by
    have he : A+C (t : ℂ)*B = (P-C ((t : ℂ)*b)*Q)+Q := by
      dsimp [A,B]; rw [map_mul]; ring
    rw [he]
    apply skew_axis P Q σ ((t : ℂ)*b) hσ hP hQ
    · simp [hb]
    · exact hA
    · rw [← he]; exact hp t
    · exact hz
  have h := rightCount_affine A B A.natDegree hp (fun t => hdn (t : ℂ)) ha
  convert h using 1
  congr 1
  dsimp [A,B]
  ring

/-- A regular generalized reduction counts the escaping root and preserves axis roots. -/
theorem reduction_counts (P Q : ℂ[X]) (σ b : ℂ) (c : ℝ) (m : ℕ)
    (hσ : σ ≠ 0) (hP : axisReflect P = C σ * P)
    (hQ : axisReflect Q = -(C σ * Q)) (hb : conj b = -b) (hc : c ≠ 0)
    (hdeg : Q.natDegree < P.natDegree) (hQd : Q.natDegree = m)
    (hrem : (P-C b*Q-C (c : ℂ)*X*Q).natDegree < m) :
    rightCount (P+Q) = rightCount (Q+(P-C b*Q-C (c : ℂ)*X*Q)) +
      (if c < 0 then 1 else 0) ∧
    axisCount (P+Q) = axisCount (Q+(P-C b*Q-C (c : ℂ)*X*Q)) := by
  let R := P-C b*Q-C (c : ℂ)*X*Q
  have hPQ : P+Q ≠ 0 := by
    intro hz
    have hh := natDegree_add_eq_left_of_natDegree_lt hdeg
    rw [hz, natDegree_zero] at hh
    omega
  have hSQ : (P-C b*Q)+Q ≠ 0 := by
    have hd : (P-C b*Q).natDegree = P.natDegree :=
      natDegree_sub_eq_left_of_natDegree_lt ((natDegree_C_mul_le _ _).trans_lt hdeg)
    intro hz
    have hh := natDegree_add_eq_left_of_natDegree_lt (hd ▸ hdeg)
    rw [hz, natDegree_zero, hd] at hh
    omega
  have hQR : Q+R ≠ 0 := by
    intro hz
    have hh := natDegree_add_eq_left_of_natDegree_lt (hQd ▸ hrem)
    change (Q+R).natDegree = Q.natDegree at hh
    rw [hz, natDegree_zero, hQd] at hh
    omega
  have hr := elimination_rightCount (P-C b*Q) Q σ hσ
    (skew_reflect P Q σ b hP hQ hb) hQ c hc m hQd hrem
  rw [skew_rightCount P Q σ b hσ hP hQ hb hdeg] at hr
  have hm (z : ℂ) (hz : z.re = 0) : (Q+R).rootMultiplicity z = (P+Q).rootMultiplicity z := by
    have he := elimination_axis_rootMultiplicity (P-C b*Q) Q σ hσ
      (skew_reflect P Q σ b hP hQ hb) hQ c hSQ
      (by simpa only [R, add_comm] using hQR) z hz
    have he' : (Q+R).rootMultiplicity z = ((P-C b*Q)+Q).rootMultiplicity z := by
      simpa only [R, add_comm] using he
    exact he'.trans (skew_axis P Q σ b hσ hP hQ hb hPQ hSQ z hz)
  refine ⟨?_, (axisCount_eq_of_rootMultiplicity _ _ hm).symm⟩
  simpa only [R, add_comm] using hr

end RouthHurwitz.ComplexRouth
