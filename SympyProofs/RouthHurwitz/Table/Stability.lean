import SympyProofs.RouthHurwitz.Table.Invariant

/-! Strict stability and the signs needed by a regular Routh reduction. -/
namespace RouthHurwitz
open Polynomial

/-- The first two coefficients of a positive-degree stable real polynomial
have the same nonzero sign. -/
theorem HurwitzStable.leading_mul_next_pos {p : Polynomial ℝ}
    (hs : HurwitzStable p) (hp : p ≠ 0) (hn : 0 < p.natDegree) :
    0 < p.leadingCoeff * p.nextCoeff := by
  let q := p.map Complex.ofRealHom
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  have hroots : q.roots ≠ 0 := by
    intro he
    have hc := (IsAlgClosed.splits q).natDegree_eq_card_roots
    simp [he, q] at hc
    omega
  have hneg : (q.roots.map Complex.re).sum < 0 := by
    have aux : ∀ s : Multiset ℂ, (∀ z ∈ s, z.re < 0) → s ≠ 0 →
        (s.map Complex.re).sum < 0 := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons z s ih =>
        intro hz _
        have hzn := hz z (by simp)
        by_cases he : s = 0
        · subst s; simpa using hzn
        · have hn := ih (fun w hw => hz w (Multiset.mem_cons_of_mem hw)) he
          simpa using add_neg hzn hn
    exact aux _ (fun z hz => hs z ((Polynomial.mem_roots hq).mp hz)) hroots
  have hv := (IsAlgClosed.splits q).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  change (p.map Complex.ofRealHom).nextCoeff =
    -(p.map Complex.ofRealHom).leadingCoeff * q.roots.sum at hv
  rw [nextCoeff_map Complex.ofRealHom.injective,
    leadingCoeff_map_of_injective Complex.ofRealHom.injective] at hv
  have he := congrArg Complex.re hv
  change p.nextCoeff = (-((p.leadingCoeff : ℝ) : ℂ) * q.roots.sum).re at he
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero] at he
  have hre : q.roots.sum.re = (q.roots.map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom q.roots
  rw [hre] at he
  have hl := leadingCoeff_ne_zero.mpr hp
  rw [he]
  nlinarith [sq_pos_of_ne_zero hl]

theorem rowPair_natDegree (d : ℕ) (u v : Row ℝ) (hu : u 0 ≠ 0) :
    (encodeRow (d+1) u + encodeRow d v).natDegree = d+1 := by
  apply le_antisymm
  · exact (natDegree_add_le _ _).trans (max_le
      (encodeRow_natDegree_le _ _) ((encodeRow_natDegree_le _ _).trans (by omega)))
  · apply le_natDegree_of_ne_zero
    simpa [coeff_encodeRow] using hu

theorem rowPair_ne_zero (d : ℕ) (u v : Row ℝ) (hu : u 0 ≠ 0) :
    encodeRow (d+1) u + encodeRow d v ≠ 0 := by
  intro hz
  have hh := rowPair_natDegree d u v hu
  rw [hz, natDegree_zero] at hh
  omega

theorem stable_pair_lower_pos (d : ℕ) (u v : Row ℝ) (hu : 0 < u 0)
    (hs : HurwitzStable (encodeRow (d+1) u + encodeRow d v)) : 0 < v 0 := by
  have hd := rowPair_natDegree d u v (ne_of_gt hu)
  have h := hs.leading_mul_next_pos (rowPair_ne_zero d u v (ne_of_gt hu)) (by omega)
  rw [leadingCoeff, nextCoeff, hd] at h
  simp [coeff_encodeRow] at h
  exact (mul_pos_iff.mp h).resolve_right (by intro hh; linarith [hh.1]) |>.2

/-- A positive regular pivot preserves strict stability under ordinary elimination. -/
theorem stable_pair_reduce (d : ℕ) (u v : Row ℝ) (hu : 0 < u 0) (hv : 0 < v 0)
    (hs : ∀ j, d+1 < 2*j → v j = 0) :
    HurwitzStable (encodeRow (d+2) u + encodeRow (d+1) v) ↔
      HurwitzStable (encodeRow (d+1) v + encodeRow d (nextRow u v)) := by
  let U := (encodeRow (d+2) u).map Complex.ofRealHom
  let V := (encodeRow (d+1) v).map Complex.ofRealHom
  let W := (encodeRow d (nextRow u v)).map Complex.ofRealHom
  let c := u 0 / v 0
  have hU : axisReflect U = C ((-1 : ℂ)^(d+2)) * U := encodeRow_axisReflect _ _
  have hV : axisReflect V = -(C ((-1 : ℂ)^(d+2)) * V) := by
    dsimp [V]; rw [encodeRow_axisReflect]; simp [pow_succ]
  have hrec : U = C (c : ℂ) * X * V + W := by
    simpa [U, V, W, c] using congrArg (Polynomial.map Complex.ofRealHom)
      (encodeRow_recurrence d u v (ne_of_gt hv) hs)
  have hrem : U - C (c : ℂ) * X * V = W := by rw [hrec]; ring
  have hVd : V.natDegree = d+1 := by simpa [V] using encodeRow_natDegree (d+1) v (ne_of_gt hv)
  have hWd : W.natDegree ≤ d := by simpa [W] using encodeRow_natDegree_le d (nextRow u v)
  have hc : 0 < c := div_pos hu hv
  have hr := elimination_rightCount U V _ (pow_ne_zero _ (by norm_num)) hU hV c
    (ne_of_gt hc) (d+1) hVd (by rw [hrem]; omega)
  rw [hrem, add_comm W V, if_neg (not_lt_of_gt hc), add_zero] at hr
  have hstart : U + V ≠ 0 := by
    rw [← Polynomial.map_add]
    exact (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr
      (rowPair_ne_zero (d+1) u v (ne_of_gt hu))
  have hend : V + W ≠ 0 := by
    rw [← Polynomial.map_add]
    exact (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr
      (rowPair_ne_zero d v (nextRow u v) (ne_of_gt hv))
  have ha (z : ℂ) (hz : z.re = 0) : (V+W).IsRoot z ↔ (U+V).IsRoot z := by
    have hm := elimination_axis_rootMultiplicity U V _ (pow_ne_zero _ (by norm_num))
      hU hV c hstart (by rw [hrem, add_comm]; exact hend) z hz
    rw [hrem, add_comm W V] at hm
    rw [← rootMultiplicity_pos hend, ← rootMultiplicity_pos hstart, hm]
  simp only [HurwitzStable, Polynomial.map_add]
  change ComplexStable (U+V) ↔ ComplexStable (V+W)
  have forward (P Q : ℂ[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
      (hcount : rightCount P = rightCount Q)
      (haxis : ∀ z : ℂ, z.re = 0 → (Q.IsRoot z ↔ P.IsRoot z)) :
      ComplexStable P → ComplexStable Q := by
    intro h z hz
    have hzero : rightCount Q = 0 := hcount ▸ (complexStable_iff_counts P hP).mp h |>.1
    have hnone : ¬ 0 < z.re := by
      intro hp
      have hm : z ∈ Q.roots.filter (fun z => 0 < z.re) := by
        exact Multiset.mem_filter.mpr ⟨(mem_roots hQ).mpr hz, hp⟩
      have hnil : Q.roots.filter (fun z => 0 < z.re) = 0 := Multiset.card_eq_zero.mp hzero
      rw [hnil] at hm
      simp at hm
    apply lt_of_le_of_ne (le_of_not_gt hnone)
    intro he
    exact (ne_of_lt (h z ((haxis z he).mp hz))) he
  exact ⟨forward _ _ hstart hend hr ha,
    forward _ _ hend hstart hr.symm (fun z hz => (ha z hz).symm)⟩

end RouthHurwitz
