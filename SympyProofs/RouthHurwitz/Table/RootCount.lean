import SympyProofs.RouthHurwitz.Roots.Limits
import SympyProofs.RouthHurwitz.Table.Repairs

/-!
# Root-count invariants for Routh operations

The proofs use the actual polynomial operations, with coefficientwise
continuous deformations. No root-count preservation premise is assumed.
-/

namespace RouthHurwitz
open Polynomial
open scoped ComplexConjugate

/-- Multiplication of the lower-degree parity component by a factor that
is positive on the imaginary axis preserves the right-half-plane count,
provided that component remains lower degree. -/
theorem parityMultiplier_rightCount (P Q α : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (hα : axisReflect α = α) (hpos : ∀ z, z.re = 0 → 0 < (α.eval z).re)
    (hdegQ : Q.natDegree < P.natDegree) (hdegαQ : (α * Q).natDegree < P.natDegree) :
    rightCount (P + α * Q) = rightCount (P + Q) := by
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  let A := P + Q
  let B := α * Q - Q
  have hdegA : A.natDegree = P.natDegree := natDegree_add_eq_left_of_natDegree_lt hdegQ
  have hdegB : B.natDegree < A.natDegree := by
    rw [hdegA]
    exact (natDegree_sub_le _ _).trans_lt (max_lt hdegαQ hdegQ)
  have hP0 : P ≠ 0 := by intro h; simp [h] at hdegQ
  have hn : 0 < A.natDegree := by rw [hdegA]; omega
  have hd (t : unitInterval) : (A + C (t : ℂ) * B).natDegree = A.natDegree :=
    natDegree_affine_of_lt A B hdegB _
  have hp (t : unitInterval) : A + C (t : ℂ) * B ≠ 0 := by
    intro h
    have hh := hd t
    rw [h, natDegree_zero] at hh
    omega
  have haxis (t : unitInterval) (z : ℂ) (hz : z.re = 0) :
      (A + C (t : ℂ) * B).rootMultiplicity z = A.rootMultiplicity z := by
    let β : ℂ[X] := 1 + C (t : ℂ) * (α - 1)
    have hβ : axisReflect β = β := by
      have ht : axisReflect (C (t : ℂ)) = C (t : ℂ) := by simp [axisReflect]
      dsimp [β]
      rw [map_add, map_one, map_mul, ht, map_sub, hα, map_one]
    have hβz : β.eval z ≠ 0 := by
      have ht0 : (0 : ℝ) ≤ t := t.property.1
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      have hreal : (β.eval z).re = 1 + (t : ℝ) * ((α.eval z).re - 1) := by
        simp [β, Complex.mul_re]
      have hpositive : 0 < (β.eval z).re := by
        rw [hreal]
        by_cases ht : (t : ℝ) = 0
        · simp [ht]
        · have htpos : (0 : ℝ) < t := lt_of_le_of_ne ht0 (Ne.symm ht)
          nlinarith [mul_pos htpos (hpos z hz)]
      intro hh
      simp [hh] at hpositive
    have he : A + C (t : ℂ) * B = P + β * Q := by dsimp [A, B, β]; ring
    rw [he]
    exact parityMultiplier_axis_rootMultiplicity P Q β σ hσ hP hQ hβ hP0 hQ0 z hz hβz
  have h := rightCount_affine A B A.natDegree hp hd haxis
  have he : A + B = P + α * Q := by dsimp [A, B]; ring
  rw [he] at h
  exact h

/-- The exact signed-shift row operation preserves the right-half-plane
root count of the two-row polynomial, for any number of leading zeros. -/
theorem shiftRow_rightCount (d w k : ℕ) (previous raw : Row ℝ)
    (hpivot : previous 0 ≠ 0) (hk : 2 * k ≤ d) (hw : d / 2 < w)
    (hz : ∀ j < k, raw j = 0) (hs : ∀ j, d < 2 * j → raw j = 0) :
    rightCount ((encodeRow (d + 1) previous + encodeRow d (shiftRow w k raw)).map Complex.ofRealHom) =
      rightCount ((encodeRow (d + 1) previous + encodeRow d raw).map Complex.ofRealHom) := by
  let P := (encodeRow (d + 1) previous).map Complex.ofRealHom
  let Q := (encodeRow d raw).map Complex.ofRealHom
  let α := (shiftMultiplier k).map Complex.ofRealHom
  have hP : axisReflect P = C ((-1 : ℂ) ^ (d + 1)) * P := encodeRow_axisReflect _ _
  have hQ : axisReflect Q = -(C ((-1 : ℂ) ^ (d + 1)) * Q) := by
    dsimp [Q]; rw [encodeRow_axisReflect]; simp [pow_succ]
  have hα : axisReflect α = α := by simp [α, shiftMultiplier, axisReflect, pow_mul]
  have hαpos (z : ℂ) (hz : z.re = 0) : 0 < (α.eval z).re := by
    have he : z = z.im * Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact shiftMultiplier_axis_positive k z.im
  have hPdeg : P.natDegree = d + 1 := by
    simpa [P] using encodeRow_natDegree (d + 1) previous hpivot
  have hQdeg : Q.natDegree ≤ d := by simpa [Q] using encodeRow_natDegree_le d raw
  have he : (encodeRow d (shiftRow w k raw)).map Complex.ofRealHom = α * Q := by
    rw [encodeRow_shiftRow d w k raw hk hw hz hs]
    simp only [Polynomial.map_mul]
    rfl
  have hαQdeg : (α * Q).natDegree ≤ d := by
    rw [← he]
    simpa using encodeRow_natDegree_le d (shiftRow w k raw)
  have h := parityMultiplier_rightCount P Q α ((-1 : ℂ) ^ (d + 1))
    (pow_ne_zero _ (by norm_num)) hP hQ hα hαpos (by omega) (by omega)
  simpa only [Polynomial.map_add, he] using h

/-- Zero-row derivative repair preserves the right-half-plane count for
an auxiliary polynomial of arbitrary degree, including repeated axis roots. -/
theorem derivativeRepair_rightCount (p : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hp : axisReflect p = C σ * p) (hn : p.natDegree ≠ 0) :
    rightCount (p + p.derivative) = rightCount p := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have hd0 : p.derivative ≠ 0 := derivative_ne_zero.mpr hn
  have hd : axisReflect p.derivative = -(C σ * p.derivative) := by
    rw [axisReflect_derivative, hp, derivative_C_mul]
  apply rightCount_add_derivative p hn
  intro t ht _
  apply axisCount_eq_of_rootMultiplicity
  intro z hz
  apply parityMultiplier_axis_rootMultiplicity p p.derivative (C (t : ℂ)) σ hσ hp hd
    (by simp [axisReflect]) hp0 hd0 z hz
  simpa using Complex.ofReal_ne_zero.mpr (ne_of_gt ht)

/-- All branches of the actual row repair preserve the right-half-plane
count. No regularity assumption is required. -/
theorem repairRow_rightCount (d w : ℕ) (previous raw : Row ℝ)
    (hpivot : previous 0 ≠ 0) (hw : d / 2 < w)
    (hs : ∀ j, d < 2 * j → raw j = 0) :
    rightCount ((encodeRow (d + 1) previous + encodeRow d (repairRow (d + 1) w previous raw)).map
      Complex.ofRealHom) =
      rightCount ((encodeRow (d + 1) previous + encodeRow d raw).map Complex.ofRealHom) := by
  by_cases hn : (nonzeroIndices w raw).Nonempty
  · by_cases hz : raw 0 = 0
    · simp only [repairRow, if_pos hn, if_pos hz]
      apply shiftRow_rightCount _ _ _ _ _ hpivot _ hw (before_firstNonzero w raw hn) hs
      by_contra! hh
      exact (firstNonzero_spec w raw hn).2 (hs _ hh)
    · simp [repairRow, hn, hz]
  have hz : ∀ j, raw j = 0 := by
    intro j
    by_cases hj : j < w
    · by_contra hh
      exact hn ⟨j, by simp [nonzeroIndices, hj, hh]⟩
    · apply hs
      omega
  have hraw : encodeRow d raw = 0 := by
    ext j
    simp [coeff_encodeRow, hz]
  have hder : encodeRow d (derivativeRow (d + 1) previous) =
      (encodeRow (d + 1) previous).derivative := by
    simpa using (encodeRow_derivative (d + 1) previous).symm
  rw [repairRow, if_neg hn, hraw, add_zero, hder]
  have hdeg : (encodeRow (d + 1) previous).natDegree = d + 1 :=
    encodeRow_natDegree _ _ hpivot
  rw [Polynomial.map_add, ← derivative_map]
  apply derivativeRepair_rightCount _ ((-1 : ℂ) ^ (d + 1))
    (pow_ne_zero _ (by norm_num)) (encodeRow_axisReflect _ _)
  simp [hdeg]

/-- The ordinary Routh reduction counts exactly the root escaping to infinity.
Opposite pivot signs contribute one right-half-plane root; equal signs
contribute none. Existing imaginary-axis roots may have arbitrary multiplicity. -/
theorem elimination_rightCount (P Q : ℂ[X]) (σ : ℂ) (hσ : σ ≠ 0)
    (hP : axisReflect P = C σ * P) (hQ : axisReflect Q = -(C σ * Q))
    (c : ℝ) (hc : c ≠ 0) (m : ℕ) (hQd : Q.natDegree = m)
    (hRd : (P - C (c : ℂ) * X * Q).natDegree < m) :
    rightCount (P + Q) = rightCount (P - C (c : ℂ) * X * Q + Q) +
      if c < 0 then 1 else 0 := by
  let D := C (c : ℂ) * X * Q
  let E := P - D + Q
  let F (t : ℝ) := E + C (t : ℂ) * D
  have hm : 0 < m := Nat.zero_lt_of_lt hRd
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQd; omega
  have hEd : E.natDegree = m := by
    dsimp [E, D]
    rw [add_comm]
    exact (natDegree_add_eq_left_of_natDegree_lt (hQd ▸ hRd)).trans hQd
  have hE0 : E ≠ 0 := by intro h; simp [h] at hEd; omega
  have hDd : D.natDegree = m + 1 := by
    dsimp [D]
    rw [mul_assoc, natDegree_C_mul (Complex.ofReal_ne_zero.mpr hc),
      natDegree_mul X_ne_zero hQ0, natDegree_X, hQd]
    omega
  have hFn (t : ℝ) : F t ≠ 0 := by
    by_cases ht : t = 0
    · simpa [F, ht] using hE0
    have hd : (F t).natDegree = m + 1 := by
      dsimp [F]
      rw [add_comm]
      apply (natDegree_add_eq_left_of_natDegree_lt ?_).trans
        ((natDegree_C_mul (Complex.ofReal_ne_zero.mpr ht)).trans hDd)
      rw [natDegree_C_mul (Complex.ofReal_ne_zero.mpr ht), hDd, hEd]
      omega
    intro hh
    simp [hh] at hd
  have hFle (t : ℝ) : (F t).natDegree ≤ m + 1 :=
    (natDegree_add_le _ _).trans (max_le (by omega) ((natDegree_C_mul_le _ _).trans hDd.le))
  have hF1 : F 1 = P + Q := by dsimp [F, E, D]; simp; ring
  have hF0 : F 0 = E := by simp [F]
  have hstart : P + Q ≠ 0 := hF1 ▸ hFn 1
  have haxisF (t : ℝ) (z : ℂ) (hz : z.re = 0) :
      (F t).rootMultiplicity z = E.rootMultiplicity z := by
    have he (t : ℝ) : F t = P - C (((1 - t) * c : ℝ) : ℂ) * X * Q + Q := by
      dsimp [F, E, D]
      push_cast
      simp only [C_mul, C_sub, C_1]
      ring
    have hh (t : ℝ) := elimination_axis_rootMultiplicity P Q σ hσ hP hQ
      ((1 - t) * c) hstart (he t ▸ hFn t) z hz
    simp_rw [← he] at hh
    exact (hh t).trans (by simpa [hF0] using (hh 0).symm)
  let g := E.reverse
  let B := reflect (m + 1) D
  have hA : reflect (m + 1) E = X * g := by
    rw [reflect_eq_reverse_mul_X_pow E (m + 1) (by omega), hEd]
    simp [g, mul_comm]
  have hG (t : ℝ) : X * g + C (t : ℂ) * B = reflect (m + 1) (F t) := by
    dsimp [F, B]
    rw [reflect_add, reflect_C_mul, hA]
  have hg : g.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hE0
  have hB : B.eval 0 = (c : ℂ) * g.eval 0 := by
    have hElc : E.leadingCoeff = Q.leadingCoeff :=
      leadingCoeff_add_of_degree_lt (degree_lt_degree (hQd ▸ hRd))
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]
    dsimp [D]
    rw [mul_assoc, coeff_C_mul, coeff_X_mul, ← hQd, coeff_natDegree,
      ← hElc, ← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  have hp (t : unitInterval) : X * g + C (t : ℂ) * B ≠ 0 := by
    rw [hG]
    exact reflect_eq_zero_iff.not.mpr (hFn t)
  have hd (t : unitInterval) : (X * g + C (t : ℂ) * B).natDegree =
      m + 1 - E.rootMultiplicity 0 := by
    rw [hG, natDegree_reflect_of_le _ (hFn t) _ (hFle t), haxisF t 0 (by simp)]
  have ha (t : unitInterval) (z : ℂ) (hz : z.re = 0) (hz0 : z ≠ 0) :
      (X * g + C (t : ℂ) * B).rootMultiplicity z = (X * g).rootMultiplicity z := by
    rw [hG, ← hA, rootMultiplicity_reflect _ _ (hFle t) z hz0,
      rootMultiplicity_reflect E (m + 1) (by omega) z hz0]
    exact haxisF t z⁻¹ (by simp [Complex.inv_re, hz])
  have hh := rightCount_affine_simple_zero g B hg c hc hB
    (m + 1 - E.rootMultiplicity 0) hp hd ha
  have hG1 : X * g + B = reflect (m + 1) (P + Q) := by simpa [hF1] using hG 1
  rw [hG1, ← hA, rightCount_reflect _ _ (by simpa [hF1] using hFle 1),
    rightCount_reflect E (m + 1) (by omega)] at hh
  exact hh

/-- One complete computed elimination-and-repair step counts the pivot sign
change, including both exceptional repair branches. -/
theorem eliminationRepair_rightCount (d w : ℕ) (upper lower : Row ℝ)
    (hu0 : upper 0 ≠ 0) (hv0 : lower 0 ≠ 0) (hw : d / 2 < w)
    (hu : ∀ j, d + 2 < 2 * j → upper j = 0)
    (hv : ∀ j, d + 1 < 2 * j → lower j = 0) :
    let raw := boundedNextRow w upper lower
    rightCount ((encodeRow (d + 2) upper + encodeRow (d + 1) lower).map Complex.ofRealHom) =
      rightCount ((encodeRow (d + 1) lower + encodeRow d (repairRow (d + 1) w lower raw)).map
        Complex.ofRealHom) + if upper 0 / lower 0 < 0 then 1 else 0 := by
  dsimp only
  let raw := boundedNextRow w upper lower
  have hr : ∀ j, d < 2 * j → raw j = 0 := by
    intro j hj
    dsimp [raw, boundedNextRow]
    split
    · exact nextRow_zero upper lower j (hu (j + 1) (by omega)) (hv (j + 1) (by omega))
    · rfl
  have hrec := encodeRow_recurrence d upper lower hv0 hv
  have he : encodeRow d (nextRow upper lower) = encodeRow d raw := by
    apply encodeRow_congr
    intro j hj
    simp [raw, boundedNextRow, show j < w by omega]
  rw [he] at hrec
  let U := (encodeRow (d + 2) upper).map Complex.ofRealHom
  let V := (encodeRow (d + 1) lower).map Complex.ofRealHom
  let W := (encodeRow d raw).map Complex.ofRealHom
  let c := upper 0 / lower 0
  have hU : axisReflect U = C ((-1 : ℂ) ^ (d + 2)) * U := encodeRow_axisReflect _ _
  have hV : axisReflect V = -(C ((-1 : ℂ) ^ (d + 2)) * V) := by
    dsimp [V]
    rw [encodeRow_axisReflect]
    simp [pow_succ]
  have hrec' : U = C (c : ℂ) * X * V + W := by
    simpa [U, V, W, c] using congrArg (Polynomial.map Complex.ofRealHom) hrec
  have hrem : U - C (c : ℂ) * X * V = W := by rw [hrec']; ring
  have hVd : V.natDegree = d + 1 := by simpa [V] using encodeRow_natDegree (d + 1) lower hv0
  have hWd : W.natDegree ≤ d := by simpa [W] using encodeRow_natDegree_le d raw
  have h := elimination_rightCount U V _ (pow_ne_zero _ (by norm_num)) hU hV c
    (div_ne_zero hu0 hv0) (d + 1) hVd (by rw [hrem]; omega)
  rw [hrem, add_comm W V] at h
  have hh := repairRow_rightCount d w lower raw hv0 hw hr
  simp only [Polynomial.map_add] at hh ⊢
  exact h.trans (congrArg (fun k => k + if c < 0 then 1 else 0) hh.symm)

end RouthHurwitz
