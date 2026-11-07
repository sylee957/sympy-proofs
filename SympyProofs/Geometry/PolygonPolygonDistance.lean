module

public import SympyProofs.Geometry.Polygon

/-!
# Exact polygon-to-polygon boundary distance

The formulas in this file use real arithmetic, `min`, `max`, square roots,
and `Real.sign`. Coordinate comparisons occur in proofs, not in the formulas.

For segments `AB` and `CD`, put `u = B - A`, `v = C - D`, and `w = A - C`.
Their squared pointwise distance is the quadratic
`F(s,t) = a*s² + 2*b*s*t + c*t² + 2*d*s + 2*e*t + k`, where
`a = u·u`, `b = u·v`, `c = v·v`, `d = u·w`, `e = v·w`, and `k = w·w`.
Write `κ(x) = min 1 (max 0 x)`, `ρ(x) = x / (x² + 1 - sign(x²))`, and
`Δ = a*c - b²`. Evaluate `F` at these five parameter pairs:

* `(0, κ(-e*ρ(c)))` and `(1, κ(-(b+e)*ρ(c)))`;
* `(κ(-d*ρ(a)), 0)` and `(κ(-(b+d)*ρ(a)), 1)`;
* `(κ((b*e-c*d)*ρ(Δ)), κ((b*d-a*e)*ρ(Δ)))`.

The square root of their minimum is the segment distance. Every candidate
is feasible. At an interior minimizer, either the stationary equations give
the fifth candidate or a flat direction reaches a side with the same value.
This also covers parallel and zero-length segments. The denominator of `ρ`
is always positive; `κ` also has an absolute-value-only expression.

`polygonPolygonDistance` takes the finite minimum over all edge pairs, using
five candidates per pair. Its inputs are `Polygon Point2D m` and
`Polygon Point2D n` with positive vertex counts. No convexity, simplicity,
orientation, or nondegeneracy hypotheses are needed. The sets are polygon
boundaries, so strict nesting can give a positive distance. The correctness
theorem identifies this finite expression with `SympyGeometry.distance` and
also proves that a closest pair exists.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

namespace PolygonDistance

/-- Clamp a real parameter to the closed unit interval. -/
def clamp (t : ℝ) : ℝ := min 1 (max 0 t)

theorem clamp_mem (t : ℝ) : clamp t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem clamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp t = t := by
  simp [clamp, max_eq_right ht.1, min_eq_right ht.2]

/-- Clamping can also be written using arithmetic and absolute values alone. -/
theorem clamp_eq_abs (t : ℝ) : clamp t = (1 + |t| - |t - 1|) / 2 := by
  rcases le_total t 0 with ht | ht
  · rw [clamp, max_eq_left ht, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
      abs_of_nonpos ht, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    ring
  · rcases le_total t 1 with ht1 | ht1
    · rw [clamp, max_eq_right ht, min_eq_right ht1, abs_of_nonneg ht,
        abs_of_nonpos (by linarith : t - 1 ≤ 0)]
      ring
    · rw [clamp, max_eq_right ht, min_eq_left ht1, abs_of_nonneg ht,
        abs_of_nonneg (by linarith : 0 ≤ t - 1)]
      ring

/-- A reciprocal expressed with a denominator that is positive even at zero. -/
def safeInv (x : ℝ) : ℝ := x / (x ^ 2 + 1 - Real.sign (x ^ 2))

theorem safeInv_denom_pos (x : ℝ) : 0 < x ^ 2 + 1 - Real.sign (x ^ 2) := by
  by_cases hx : x = 0
  · simp [hx]
  · have h := sq_pos_of_ne_zero hx
    simpa [Real.sign_of_pos h] using h

theorem safeInv_eq_inv (x : ℝ) : safeInv x = x⁻¹ := by
  by_cases hx : x = 0
  · simp [safeInv, hx]
  · rw [safeInv, Real.sign_of_pos (sq_pos_of_ne_zero hx)]
    field_simp
    ring

private theorem clamp_sq_le (u t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (clamp u - u) ^ 2 ≤ (t - u) ^ 2 := by
  rcases le_total 0 u with hu | hu
  · rw [clamp, max_eq_right hu]
    rcases le_total u 1 with hu1 | hu1
    · simp [min_eq_right hu1, sq_nonneg]
    · rw [min_eq_left hu1]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
        (show 0 ≤ 2 * u - t - 1 by linarith [ht.2])]
  · rw [clamp, max_eq_left hu, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith [mul_nonneg ht.1 (neg_nonneg.mpr hu)]

private theorem quadratic_clamp_le (a b c : ℝ) (ha : 0 ≤ a)
    (hz : a = 0 → b = 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let u := clamp (-b * safeInv a)
    a * u ^ 2 + 2 * b * u + c ≤ a * t ^ 2 + 2 * b * t + c := by
  dsimp only
  by_cases ha0 : a = 0
  · simp [ha0, hz ha0]
  · have hmul : a * (-b * safeInv a) = -b := by
      rw [safeInv_eq_inv]
      field_simp
    have h := mul_le_mul_of_nonneg_left (clamp_sq_le (-b * safeInv a) t ht) ha
    have hm := congrArg (fun z => z * (t - clamp (-b * safeInv a))) hmul
    nlinarith [hm]

/-- Coefficients of a real quadratic in two scalar parameters. -/
structure Quadratic where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  k : ℝ

/-- Evaluate `a*s² + 2*b*s*t + c*t² + 2*d*s + 2*e*t + k`. -/
def Quadratic.eval (q : Quadratic) (s t : ℝ) : ℝ :=
  q.a * s ^ 2 + 2 * q.b * s * t + q.c * t ^ 2 + 2 * q.d * s + 2 * q.e * t + q.k

/-- Determinant of the quadratic coefficient matrix. -/
def Quadratic.det (q : Quadratic) : ℝ := q.a * q.c - q.b ^ 2

/-- Four side minimizers and a clamped stationary point, all in the unit square. -/
def Quadratic.candidate (q : Quadratic) : Fin 5 → ℝ × ℝ :=
  ![(0, clamp (-q.e * safeInv q.c)),
    (1, clamp (-(q.b + q.e) * safeInv q.c)),
    (clamp (-q.d * safeInv q.a), 0),
    (clamp (-(q.b + q.d) * safeInv q.a), 1),
    (clamp ((q.b * q.e - q.c * q.d) * safeInv q.det),
      clamp ((q.b * q.d - q.a * q.e) * safeInv q.det))]

private theorem Quadratic.candidate_mem (q : Quadratic) (i : Fin 5) :
    (q.candidate i).1 ∈ Set.Icc (0 : ℝ) 1 ∧
      (q.candidate i).2 ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> dsimp [candidate] <;>
    exact ⟨by first | exact clamp_mem _ | norm_num,
      by first | exact clamp_mem _ | norm_num⟩

private theorem Quadratic.stationary (q : Quadratic) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      q.eval s t ≤ q.eval u v) :
    q.a * s + q.b * t + q.d = 0 ∧ q.b * s + q.c * t + q.e = 0 := by
  have hsmin : IsLocalMin (fun u => q.eval u t) s :=
    (show IsMinOn (fun u => q.eval u t) (Set.Icc 0 1) s from
      fun u hu => hmin u hu t ⟨ht.1.le, ht.2.le⟩).isLocalMin (Icc_mem_nhds hs.1 hs.2)
  have htmin : IsLocalMin (fun v => q.eval s v) t :=
    (show IsMinOn (fun v => q.eval s v) (Set.Icc 0 1) t from
      fun v hv => hmin s ⟨hs.1.le, hs.2.le⟩ v hv).isLocalMin (Icc_mem_nhds ht.1 ht.2)
  have hsd : HasDerivAt (fun u => q.eval u t)
      (2 * (q.a * s + q.b * t + q.d)) s := by
    have h1 := ((hasDerivAt_id s).pow 2).const_mul q.a
    have h2 := ((hasDerivAt_id s).const_mul (2 * q.b)).mul_const t
    have h3 := (hasDerivAt_id s).const_mul (2 * q.d)
    convert (((h1.add h2).add_const (q.c * t ^ 2)).add h3).add_const
      (2 * q.e * t + q.k) using 1 <;> dsimp [eval] <;>
      first | (funext u; ring) | ring
  have htd : HasDerivAt (fun v => q.eval s v)
      (2 * (q.b * s + q.c * t + q.e)) t := by
    have h1 := (hasDerivAt_id t).const_mul (2 * q.b * s)
    have h2 := ((hasDerivAt_id t).pow 2).const_mul q.c
    have h3 := (hasDerivAt_id t).const_mul (2 * q.e)
    convert ((((h1.const_add (q.a * s ^ 2)).add h2).add_const
      (2 * q.d * s)).add h3).add_const q.k using 1 <;> dsimp [eval]; ring
  constructor <;> linarith [hsmin.hasDerivAt_eq_zero hsd, htmin.hasDerivAt_eq_zero htd]

private theorem path_to_boundary (s t r : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ l ∈ Set.Icc (0 : ℝ) 1,
      ((1 - l) * s + l * r) ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1 - l) * t) ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1 - l) * s + l * r = 0 ∨ (1 - l) * s + l * r = 1 ∨ (1 - l) * t = 0) := by
  have hc : ContinuousOn (fun l : ℝ => (1 - l) * s + l * r) (Set.Icc 0 1) := by
    fun_prop
  have hv (l : ℝ) (hl : l ∈ Set.Icc (0 : ℝ) 1) : (1 - l) * t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hl.2) ht.1
    · nlinarith [ht.2, mul_nonneg hl.1 ht.1]
  by_cases hr0 : 0 ≤ r
  · by_cases hr1 : r ≤ 1
    · exact ⟨1, by norm_num, by simpa using And.intro hr0 hr1, by simp, by simp⟩
    · obtain ⟨l, hl, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
        (show (1 : ℝ) ∈ Set.Icc ((1 - 0) * s + 0 * r) ((1 - 1) * s + 1 * r) by
          simpa using And.intro hs.2 (le_of_not_ge hr1))
      dsimp only at he
      exact ⟨l, hl, by rw [he]; norm_num, hv l hl, Or.inr (Or.inl he)⟩
  · obtain ⟨l, hl, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Set.Icc ((1 - 1) * s + 1 * r) ((1 - 0) * s + 0 * r) by
        simpa using And.intro (le_of_not_ge hr0) hs.1)
    dsimp only at he
    exact ⟨l, hl, by rw [he]; norm_num, hv l hl, Or.inl he⟩

private theorem Quadratic.flat (q : Quadratic) (s t u v : ℝ)
    (ha : q.a ≠ 0) (hdet : q.det = 0)
    (hs : q.a * s + q.b * t + q.d = 0)
    (ht : q.b * s + q.c * t + q.e = 0)
    (hline : q.a * (u - s) + q.b * (v - t) = 0) : q.eval u v = q.eval s t := by
  have hid : q.a * (q.eval u v - q.eval s t) =
      (q.a * (u - s) + q.b * (v - t)) ^ 2 + q.det * (v - t) ^ 2 +
      2 * q.a * (q.a * s + q.b * t + q.d) * (u - s) +
      2 * q.a * (q.b * s + q.c * t + q.e) * (v - t) := by
    dsimp [eval, det]
    ring
  rw [hs, ht, hline, hdet] at hid
  have hz : q.a * (q.eval u v - q.eval s t) = 0 := by simpa using hid
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)

/-- Conditions on coordinate slices satisfied by squared affine residuals. -/
def Quadratic.Admissible (q : Quadratic) : Prop :=
  0 ≤ q.a ∧ 0 ≤ q.c ∧ (q.a = 0 → q.b = 0 ∧ q.d = 0) ∧
    (q.c = 0 → q.b = 0 ∧ q.e = 0)

private theorem Quadratic.boundary_candidate (q : Quadratic) (hq : q.Admissible)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hb : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    ∃ i : Fin 5, q.eval (q.candidate i).1 (q.candidate i).2 ≤ q.eval s t := by
  rcases hq with ⟨ha, hc, ha0, hc0⟩
  rcases hb with rfl | rfl | rfl | rfl
  · refine ⟨0, ?_⟩
    simpa [eval, candidate] using quadratic_clamp_le q.c q.e q.k hc
      (fun h => (hc0 h).2) t ht
  · refine ⟨1, ?_⟩
    have h := quadratic_clamp_le q.c (q.b + q.e) (q.a + 2 * q.d + q.k) hc
      (fun h => by simp [(hc0 h).1, (hc0 h).2]) t ht
    dsimp [candidate, eval]
    dsimp only at h
    nlinarith [h]
  · refine ⟨2, ?_⟩
    simpa [eval, candidate] using quadratic_clamp_le q.a q.d q.k ha
      (fun h => (ha0 h).2) s hs
  · refine ⟨3, ?_⟩
    have h := quadratic_clamp_le q.a (q.b + q.d) (q.c + 2 * q.e + q.k) ha
      (fun h => by simp [(ha0 h).1, (ha0 h).2]) s hs
    dsimp [candidate, eval]
    dsimp only at h
    nlinarith [h]

private theorem Quadratic.exists_candidate_le (q : Quadratic) (hq : q.Admissible)
    (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin 5, q.eval (q.candidate i).1 (q.candidate i).2 ≤ q.eval u v := by
  have hc : Continuous (fun z : ℝ × ℝ => q.eval z.1 z.2) := by
    unfold eval
    fun_prop
  obtain ⟨⟨s, t⟩, ⟨hs, ht⟩, hm⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
      (show (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).Nonempty from
        ⟨(0, 0), by norm_num⟩) hc.continuousOn
  have hmin (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : q.eval s t ≤ q.eval x y :=
    hm (show (x, y) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 from ⟨hx, hy⟩)
  suffices ∃ i : Fin 5, q.eval (q.candidate i).1 (q.candidate i).2 ≤ q.eval s t by
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi.trans (hmin u hu v hv)⟩
  by_cases hb : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1
  · exact q.boundary_candidate hq s t hs ht hb
  have hsi : s ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [Set.mem_Icc] at hs
    simp only [not_or] at hb
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hb.1), lt_of_le_of_ne hs.2 hb.2.1⟩
  have hti : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [Set.mem_Icc] at ht
    simp only [not_or] at hb
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hb.2.2.1), lt_of_le_of_ne ht.2 hb.2.2.2⟩
  obtain ⟨hgs, hgt⟩ := q.stationary s t hsi hti hmin
  by_cases hd : q.det = 0
  · by_cases ha : q.a = 0
    · obtain ⟨hb, hd⟩ := hq.2.2.1 ha
      obtain ⟨i, hi⟩ := q.boundary_candidate hq 0 t (by norm_num) ht (Or.inl rfl)
      exact ⟨i, by simpa [eval, ha, hb, hd] using hi⟩
    · obtain ⟨l, _, hx, hy, hboundary⟩ := path_to_boundary s t (s + q.b * t / q.a) hs ht
      have hline : q.a * ((1 - l) * s + l * (s + q.b * t / q.a) - s) +
          q.b * ((1 - l) * t - t) = 0 := by
        field_simp
        ring
      have he := q.flat s t _ _ ha hd hgs hgt hline
      obtain ⟨i, hi⟩ := q.boundary_candidate hq _ _ hx hy
        (hboundary.imp_right (fun h => h.imp_right Or.inl))
      exact ⟨i, he ▸ hi⟩
  · have hse : s = (q.b * q.e - q.c * q.d) * safeInv q.det := by
      rw [safeInv_eq_inv, ← div_eq_mul_inv]
      apply (eq_div_iff hd).mpr
      dsimp [det]
      linear_combination q.c * hgs - q.b * hgt
    have hte : t = (q.b * q.d - q.a * q.e) * safeInv q.det := by
      rw [safeInv_eq_inv, ← div_eq_mul_inv]
      apply (eq_div_iff hd).mpr
      dsimp [det]
      linear_combination q.a * hgt - q.b * hgs
    refine ⟨4, ?_⟩
    dsimp [candidate]
    rw [← hse, ← hte, clamp_of_mem hs, clamp_of_mem ht]

/-- The finite minimum of the five candidate values. -/
def Quadratic.minimum (q : Quadratic) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin 5 => q.eval (q.candidate i).1 (q.candidate i).2)

/-- Expand the fixed-size minimum into five scalar expressions. -/
theorem Quadratic.minimum_eq_min (q : Quadratic) :
    let f := fun i : Fin 5 => q.eval (q.candidate i).1 (q.candidate i).2
    q.minimum = min (f 0) (min (f 1) (min (f 2) (min (f 3) (f 4)))) := by
  dsimp only
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_univ 0))
      (le_min (Finset.inf'_le _ (Finset.mem_univ 1))
        (le_min (Finset.inf'_le _ (Finset.mem_univ 2))
          (le_min (Finset.inf'_le _ (Finset.mem_univ 3))
            (Finset.inf'_le _ (Finset.mem_univ 4)))))
  · apply Finset.le_inf'
    intro i _
    fin_cases i <;> simp [min_le_iff]

private theorem Quadratic.minimum_le (q : Quadratic) (hq : q.Admissible)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    q.minimum ≤ q.eval s t := by
  obtain ⟨i, hi⟩ := q.exists_candidate_le hq s t hs ht
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans hi

private theorem Quadratic.minimum_attained (q : Quadratic) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, q.eval s t = q.minimum := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun i : Fin 5 => q.eval (q.candidate i).1 (q.candidate i).2)
  exact ⟨(q.candidate i).1, (q.candidate_mem i).1,
    (q.candidate i).2, (q.candidate_mem i).2, hi.symm⟩

/-- Squared distance between the segment points at parameters `s` and `t`. -/
def segmentQuadratic (A B C D : Point2D) : Quadratic where
  a := (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2
  b := (B 0 - A 0) * (C 0 - D 0) + (B 1 - A 1) * (C 1 - D 1)
  c := (C 0 - D 0) ^ 2 + (C 1 - D 1) ^ 2
  d := (B 0 - A 0) * (A 0 - C 0) + (B 1 - A 1) * (A 1 - C 1)
  e := (C 0 - D 0) * (A 0 - C 0) + (C 1 - D 1) * (A 1 - C 1)
  k := (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2

private theorem segmentQuadratic_admissible (A B C D : Point2D) :
    (segmentQuadratic A B C D).Admissible := by
  refine ⟨by dsimp [segmentQuadratic]; positivity,
    by dsimp [segmentQuadratic]; positivity, ?_, ?_⟩
  · intro h
    dsimp [segmentQuadratic] at h ⊢
    have hx : B 0 - A 0 = 0 := by nlinarith [sq_nonneg (B 1 - A 1)]
    have hy : B 1 - A 1 = 0 := by nlinarith [sq_nonneg (B 0 - A 0)]
    simp [hx, hy]
  · intro h
    dsimp [segmentQuadratic] at h ⊢
    have hx : C 0 - D 0 = 0 := by nlinarith [sq_nonneg (C 1 - D 1)]
    have hy : C 1 - D 1 = 0 := by nlinarith [sq_nonneg (C 0 - D 0)]
    simp [hx, hy]

private theorem segmentQuadratic_eval (A B C D : Point2D) (s t : ℝ) :
    (segmentQuadratic A B C D).eval s t =
      dist ((1 - s) • A + s • B) ((1 - t) • C + t • D) ^ 2 := by
  rw [dist_sq_pointDistanceSq]
  simp [segmentQuadratic, Quadratic.eval, pointDistanceSq]
  ring

end PolygonDistance

open PolygonDistance

/-- Squared segment distance: the minimum of five explicit quadratic values.
Four candidates project an endpoint onto the opposite segment; the fifth
clamps the stationary parameters of the two supporting lines. All candidates
lie on the segments, including for parallel lines or coincident endpoints. -/
def segmentSegmentDistanceSq (A B C D : Point2D) : ℝ :=
  (segmentQuadratic A B C D).minimum

/-- An exact closed formula for the distance between two closed planar segments. -/
def segmentSegmentDistance (A B C D : Point2D) : ℝ :=
  Real.sqrt (segmentSegmentDistanceSq A B C D)

theorem segmentSegmentDistanceSq_nonneg (A B C D : Point2D) :
    0 ≤ segmentSegmentDistanceSq A B C D := by
  obtain ⟨s, _, t, _, he⟩ := (segmentQuadratic A B C D).minimum_attained
  rw [segmentSegmentDistanceSq, ← he, segmentQuadratic_eval]
  exact sq_nonneg _

/-- The formula is an attained minimum over all pairs of segment points. -/
theorem segment_segment_isLeast (A B C D : Point2D) :
    IsLeast {r | ∃ X ∈ segment A B, ∃ Y ∈ segment C D, dist X Y = r}
      (segmentSegmentDistance A B C D) := by
  constructor
  · obtain ⟨s, hs, t, ht, he⟩ := (segmentQuadratic A B C D).minimum_attained
    refine ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, ?_⟩
    rw [segmentSegmentDistance, segmentSegmentDistanceSq, ← he,
      segmentQuadratic_eval, Real.sqrt_sq dist_nonneg]
  · rintro r ⟨X, ⟨s, hs, rfl⟩, Y, ⟨t, ht, rfl⟩, rfl⟩
    have h := (segmentQuadratic A B C D).minimum_le
      (segmentQuadratic_admissible A B C D) s t hs ht
    rw [segmentQuadratic_eval] at h
    simpa [segmentSegmentDistance, segmentSegmentDistanceSq] using Real.sqrt_le_sqrt h

/-- Correctness with respect to the infimum-based set distance. No nondegeneracy
or nonintersection hypotheses are needed. -/
theorem segment_segment_distance (A B C D : Point2D) :
    distance (segment A B) (segment C D) = segmentSegmentDistance A B C D :=
  (segment_segment_isLeast A B C D).csInf_eq

/-- A finite closed formula for polygon boundary distance. There are five
quadratic candidates per edge pair. The vertex counts must be positive;
convexity, simplicity, and distinct adjacent vertices are not required.
All coordinate arithmetic, regularized reciprocals, clamped parameters, and
candidate values are given locally in this definition. -/
def polygonPolygonDistance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ((i, j) : Fin m × Fin n) =>
    let A := p i
    let B := p (finRotate m i)
    let C := q j
    let D := q (finRotate n j)
    let ux := B 0 - A 0
    let uy := B 1 - A 1
    let vx := C 0 - D 0
    let vy := C 1 - D 1
    let wx := A 0 - C 0
    let wy := A 1 - C 1
    let a := ux ^ 2 + uy ^ 2
    let b := ux * vx + uy * vy
    let c := vx ^ 2 + vy ^ 2
    let d := ux * wx + uy * wy
    let e := vx * wx + vy * wy
    let k := wx ^ 2 + wy ^ 2
    let Δ := a * c - b ^ 2
    let ra := a / (a ^ 2 + 1 - Real.sign (a ^ 2))
    let rc := c / (c ^ 2 + 1 - Real.sign (c ^ 2))
    let rΔ := Δ / (Δ ^ 2 + 1 - Real.sign (Δ ^ 2))
    let t₀ := min 1 (max 0 (-e * rc))
    let t₁ := min 1 (max 0 (-(b + e) * rc))
    let s₀ := min 1 (max 0 (-d * ra))
    let s₁ := min 1 (max 0 (-(b + d) * ra))
    let s := min 1 (max 0 ((b * e - c * d) * rΔ))
    let t := min 1 (max 0 ((b * d - a * e) * rΔ))
    let f := fun s t : ℝ =>
      a * s ^ 2 + 2 * b * s * t + c * t ^ 2 + 2 * d * s + 2 * e * t + k
    Real.sqrt (min (f 0 t₀) (min (f 1 t₁) (min (f s₀ 0) (min (f s₁ 1) (f s t))))))

private theorem polygonPolygonDistance_eq_min_segments {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    polygonPolygonDistance p q =
      Finset.univ.inf' Finset.univ_nonempty (fun ((i, j) : Fin m × Fin n) =>
        segmentSegmentDistance (p i) (p (finRotate m i))
          (q j) (q (finRotate n j))) := by
  unfold polygonPolygonDistance
  congr 1

/-- Some pair of points on the polygon boundaries attains the formula,
and every other pair is at least as far apart. -/
theorem polygon_polygon_isLeast {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    IsLeast {r | ∃ X ∈ p.boundary ℝ, ∃ Y ∈ q.boundary ℝ, dist X Y = r}
      (polygonPolygonDistance p q) := by
  rw [polygonPolygonDistance_eq_min_segments]
  constructor
  · obtain ⟨⟨i, j⟩, _, he⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
      Finset.univ_nonempty (fun ((i, j) : Fin m × Fin n) =>
        segmentSegmentDistance (p i) (p (finRotate m i))
          (q j) (q (finRotate n j)))
    obtain ⟨X, hX, Y, hY, hd⟩ :=
      (segment_segment_isLeast (p i) (p (finRotate m i))
        (q j) (q (finRotate n j))).1
    exact ⟨X, (Polygon.mem_boundary_iff p X).mpr ⟨i, hX⟩,
      Y, (Polygon.mem_boundary_iff q Y).mpr ⟨j, hY⟩, hd.trans he.symm⟩
  · rintro r ⟨X, hX, Y, hY, rfl⟩
    obtain ⟨i, hi⟩ := (Polygon.mem_boundary_iff p X).mp hX
    obtain ⟨j, hj⟩ := (Polygon.mem_boundary_iff q Y).mp hY
    exact (Finset.inf'_le _ (Finset.mem_univ (i, j))).trans
      ((segment_segment_isLeast (p i) (p (finRotate m i))
        (q j) (q (finRotate n j))).2 ⟨X, hi, Y, hj, rfl⟩)

/-- The closed formula equals the distance of the two boundary sets. -/
theorem polygon_polygon_distance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    distance (p.boundary ℝ) (q.boundary ℝ) = polygonPolygonDistance p q :=
  (polygon_polygon_isLeast p q).csInf_eq

theorem polygonPolygonDistance_nonneg {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    0 ≤ polygonPolygonDistance p q := by
  obtain ⟨X, _, Y, _, he⟩ := (polygon_polygon_isLeast p q).1
  exact he ▸ dist_nonneg

/-- Distance remains symmetric even when the coordinates are arbitrary real expressions. -/
theorem polygonPolygonDistance_comm {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    polygonPolygonDistance p q = polygonPolygonDistance q p := by
  apply le_antisymm
  · obtain ⟨Y, hY, X, hX, he⟩ := (polygon_polygon_isLeast q p).1
    exact (polygon_polygon_isLeast p q).2 ⟨X, hX, Y, hY, (dist_comm X Y).trans he⟩
  · obtain ⟨X, hX, Y, hY, he⟩ := (polygon_polygon_isLeast p q).1
    exact (polygon_polygon_isLeast q p).2 ⟨Y, hY, X, hX, (dist_comm Y X).trans he⟩

/-- Zero distance detects intersection of the boundaries, including crossing edges. -/
theorem polygonPolygonDistance_eq_zero_iff {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    polygonPolygonDistance p q = 0 ↔ ∃ X, X ∈ p.boundary ℝ ∧ X ∈ q.boundary ℝ := by
  constructor
  · intro h
    obtain ⟨X, hX, Y, hY, he⟩ := (polygon_polygon_isLeast p q).1
    have hXY := dist_eq_zero.mp (he.trans h)
    exact ⟨X, hX, hXY ▸ hY⟩
  · rintro ⟨X, hX, hY⟩
    exact le_antisymm ((polygon_polygon_isLeast p q).2 ⟨X, hX, X, hY, dist_self X⟩)
      (polygonPolygonDistance_nonneg p q)

/-- A symbolic parallel-edge example, valid for every real offset. -/
theorem segmentSegmentDistance_parallel_horizontal (h : ℝ) :
    segmentSegmentDistance !₂[0, 0] !₂[1, 0] !₂[0, h] !₂[1, h] = |h| := by
  simp [segmentSegmentDistance, segmentSegmentDistanceSq, Quadratic.minimum_eq_min,
    Quadratic.candidate, Quadratic.eval, Quadratic.det, segmentQuadratic,
    safeInv_eq_inv, clamp]
  norm_num [Real.sqrt_sq_eq_abs]

/-- Intersections in the interiors of both segments are among the candidates. -/
theorem segmentSegmentDistance_crossed :
    segmentSegmentDistance !₂[0, 0] !₂[1, 1] !₂[0, 1] !₂[1, 0] = 0 := by
  norm_num [segmentSegmentDistance, segmentSegmentDistanceSq, Quadratic.minimum_eq_min,
    Quadratic.candidate, Quadratic.eval, Quadratic.det, segmentQuadratic,
    safeInv_eq_inv, clamp]

/-- Collapsing both segments recovers ordinary point distance. -/
theorem segmentSegmentDistance_points (A C : Point2D) :
    segmentSegmentDistance A A C C = dist A C := by
  rw [point_distance_coordinates]
  simp [segmentSegmentDistance, segmentSegmentDistanceSq, Quadratic.minimum_eq_min,
    Quadratic.candidate, Quadratic.eval, Quadratic.det, segmentQuadratic,
    safeInv_eq_inv, clamp, pointDistanceSq]

end

end SympyGeometry
