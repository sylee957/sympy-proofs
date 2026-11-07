module

public import SympyProofs.Geometry.PolygonInterior
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Covering.FundamentalGroupCircle

/-!
# Winding numbers of polygonal paths

The winding number is defined by total angular change, not by a crossing
test. Away from the polygonal path it is an integer, agrees with the signed
crossing sum, and its parity characterizes the odd–even filled region.

Writing `zᵢ = (pᵢ.x - X.x) + I * (pᵢ.y - X.y)`, the formula is
`W(p,X) = (∑ i, arg (zᵢ₊₁ / zᵢ)) / (2 * π)`.
Each edge avoiding `X` has its ratio in the slit plane, so the principal
argument follows a continuous lift along the whole straight edge.
`windingNumber_eq_topological` identifies this formula with Mathlib's
`AddCircle.windingNumber` of the concatenated direction loop.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

open Classical Set
open scoped Topology

namespace PolygonWinding

/-- The vector from the query point to a vertex, in complex coordinates. -/
def vector (A X : Point2D) : ℂ := ⟨A 0 - X 0, A 1 - X 1⟩

theorem vector_ne_zero {A B X : Point2D} (hX : X ∉ segment A B) : vector A X ≠ 0 := by
  intro h
  have ha : A = X := by
    have hh := Complex.ext_iff.mp h
    ext i
    fin_cases i
    · exact sub_eq_zero.mp hh.1
    · exact sub_eq_zero.mp hh.2
  exact hX ⟨0, by norm_num, by simpa using ha⟩

private theorem not_mem_swap {A B X : Point2D} (hX : X ∉ segment A B) :
    X ∉ segment B A := by
  rintro ⟨t, ht, he⟩
  exact hX ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    by simpa [sub_sub_cancel, add_comm] using he⟩

/-- An edge avoiding the query point subtends an angle strictly between
`-π` and `π`: its endpoint ratio avoids the nonpositive real axis. -/
theorem ratio_mem_slitPlane {A B X : Point2D} (hX : X ∉ segment A B) :
    vector B X / vector A X ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  let r := vector B X / vector A X
  have hr : r.re ≤ 0 := h.1
  have hi : r.im = 0 := h.2
  have he : r * vector A X = vector B X := div_mul_cancel₀ _ (vector_ne_zero hX)
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, vector, hi,
    zero_mul, sub_zero, add_zero] at hre him
  have hd : 0 < 1 - r.re := by linarith
  apply hX
  refine ⟨1 / (1 - r.re), ⟨by positivity, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  ext i
  fin_cases i <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    dsimp at * <;> field_simp <;> nlinarith

private theorem arg_pos_iff_of_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < z.arg ↔ 0 < z.im := by
  constructor
  · intro h
    have hi := Complex.arg_nonneg_iff.mp h.le
    by_contra hn
    have he : z.im = 0 := le_antisymm (le_of_not_gt hn) hi
    have hr : 0 < z.re := (Complex.mem_slitPlane_iff.mp hz).resolve_right (not_not.mpr he)
    have ha := Complex.arg_eq_zero_iff.mpr ⟨hr.le, he⟩
    linarith
  · intro h
    have ha := Complex.arg_nonneg_iff.mpr h.le
    exact lt_of_le_of_ne ha (fun he => h.ne' (Complex.arg_eq_zero_iff.mp he.symm).2)

private theorem angle_carry (a b d : ℝ)
    (ha : -Real.pi < a ∧ a ≤ Real.pi) (hb : -Real.pi < b ∧ b ≤ Real.pi)
    (hd : -Real.pi < d ∧ d < Real.pi)
    (he : (d : Real.Angle) = ((b - a : ℝ) : Real.Angle)) :
    d = b - a + 2 * Real.pi *
      (if a < 0 then (if b < 0 then 0 else if d < 0 then -1 else 0)
       else if b < 0 then (if 0 < d then 1 else 0) else 0) := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hlo : (-2 : ℝ) < k := by nlinarith [Real.pi_pos]
  have hhi : (k : ℝ) < 2 := by nlinarith [Real.pi_pos]
  have hkl : -2 < k := by exact_mod_cast hlo
  have hkh : k < 2 := by exact_mod_cast hhi
  interval_cases k <;> norm_num at hk <;> split_ifs <;> linarith [Real.pi_pos]

/-- The angular increment is the difference of endpoint arguments plus
the signed crossing correction at the positive real axis. -/
theorem arg_ratio_eq {A B X : Point2D} (hX : X ∉ segment A B) :
    (vector B X / vector A X).arg =
      (-vector B X).arg - (-vector A X).arg +
        2 * Real.pi * PolygonInterior.edgeIndex A B X := by
  have ha := vector_ne_zero hX
  have hb := vector_ne_zero (not_mem_swap hX)
  have hs := ratio_mem_slitPlane hX
  have he : ((vector B X / vector A X).arg : Real.Angle) =
      (((-vector B X).arg - (-vector A X).arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, ← Complex.arg_div_coe_angle (neg_ne_zero.mpr hb) (neg_ne_zero.mpr ha)]
    simp
  have hc := angle_carry (-vector A X).arg (-vector B X).arg
    (vector B X / vector A X).arg (Complex.arg_mem_Ioc _) (Complex.arg_mem_Ioc _)
    ⟨Complex.neg_pi_lt_arg _, (Complex.arg_le_pi _).lt_of_ne (Complex.slitPlane_arg_ne_pi hs)⟩ he
  have him : (vector B X / vector A X).im =
      PolygonInterior.cross A B X / Complex.normSq (vector A X) := by
    simp only [Complex.div_im, vector, PolygonInterior.cross]
    ring
  have hn : 0 < Complex.normSq (vector A X) := Complex.normSq_pos.mpr ha
  have hdneg : (vector B X / vector A X).arg < 0 ↔ PolygonInterior.cross A B X < 0 := by
    rw [Complex.arg_neg_iff, him, div_neg_iff]
    simp [hn, hn.not_gt]
  have hdpos : 0 < (vector B X / vector A X).arg ↔ 0 < PolygonInterior.cross A B X := by
    rw [arg_pos_iff_of_slit hs, him, div_pos_iff_of_pos_right hn]
  have haneg : (-vector A X).arg < 0 ↔ 0 < A 1 - X 1 := by
    rw [Complex.arg_neg_iff]; simp [vector]
  have hbneg : (-vector B X).arg < 0 ↔ 0 < B 1 - X 1 := by
    rw [Complex.arg_neg_iff]; simp [vector]
  rw [hc]
  congr 1
  unfold PolygonInterior.edgeIndex
  simp only [haneg, hbneg, hdneg, hdpos, PolygonInterior.positive_eq]
  by_cases hay : 0 < A 1 - X 1 <;> by_cases hby : 0 < B 1 - X 1
  · simp [hay, hby]
  · have hd : B 1 - A 1 < 0 := by linarith
    simp [hay, hby, mul_pos_iff, hd, hd.not_gt]
  · have hd : 0 < B 1 - A 1 := by linarith
    simp [hay, hby, hd]
  · simp [hay, hby]

/-- The segment from `1` to an endpoint ratio stays in the slit plane. -/
theorem interpolatedRatio_mem_slitPlane {r : ℂ} (hr : r ∈ Complex.slitPlane)
    (t : unitInterval) : (1 - (t : ℂ)) + (t : ℂ) * r ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hr ⊢
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
    Complex.sub_im, Complex.one_im, sub_self, Complex.mul_im, zero_add, add_zero]
  rcases hr with hr | hr
  · left
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
      have := mul_pos hpos hr
      linarith [t.2.2]
  · by_cases ht : (t : ℝ) = 0
    · left; simp [ht]
    · right; exact mul_ne_zero ht hr

/-- A continuous lift of the change in direction along one straight edge.
The parameter follows the actual segment, not a constant-speed circular arc. -/
def edgeAngleLift (r : ℂ) (hr : r ∈ Complex.slitPlane) (c : ℝ) : Path c (c + r.arg) where
  toFun t := c + Complex.arg ((1 - (t : ℂ)) + (t : ℂ) * r)
  continuous_toFun := by
    apply continuous_const.add
    exact Complex.continuousOn_arg.comp_continuous
      (f := fun t : unitInterval => (1 - (t : ℂ)) + (t : ℂ) * r)
      (by fun_prop) (interpolatedRatio_mem_slitPlane hr)
  source' := by simp
  target' := by simp

/-- Projecting the edge lift gives the argument of the actual affine segment. -/
theorem edgeAngleLift_projects {a b : ℂ} (ha : a ≠ 0)
    (hr : b / a ∈ Complex.slitPlane) (c : ℝ)
    (hc : (c : Real.Angle) = a.arg) (t : unitInterval) :
    (edgeAngleLift (b / a) hr c t : Real.Angle) =
      (Complex.arg ((1 - (t : ℂ)) * a + (t : ℂ) * b) : Real.Angle) := by
  change ((c + Complex.arg ((1 - (t : ℂ)) + (t : ℂ) * (b / a)) : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, hc, add_comm, ← Complex.arg_mul_coe_angle
    (Complex.slitPlane_ne_zero (interpolatedRatio_mem_slitPlane hr t)) ha]
  congr 2
  field_simp

/-- Concatenate the continuously lifted edge arguments, carrying the endpoint
angle forward rather than reducing it modulo `2π` at each vertex. -/
def angleLiftChain : (n : ℕ) → (r : Fin n → ℂ) → (∀ i, r i ∈ Complex.slitPlane) →
    (c : ℝ) → Path c (c + ∑ i, (r i).arg)
  | 0, _, _, c => (Path.refl c).cast rfl (by simp)
  | n + 1, r, hr, c =>
    ((edgeAngleLift (r 0) (hr 0) c).trans
      (angleLiftChain n (fun i => r i.succ) (fun i => hr i.succ) (c + (r 0).arg))).cast
      rfl (by rw [Fin.sum_univ_succ]; ring)

end PolygonWinding

namespace Polygon

/-- Total signed angular change along the edges about `X`. Off the polygonal
path each principal argument is the continuous angular change along that edge. -/
def totalAngle {n : ℕ} (p : Polygon Point2D n) (X : Point2D) : ℝ :=
  ∑ i : Fin n,
    let A := p i
    let B := p (finRotate n i)
    let a : ℂ := ⟨A 0 - X 0, A 1 - X 1⟩
    let b : ℂ := ⟨B 0 - X 0, B 1 - X 1⟩
    Complex.arg (b / a)

/-- Winding number from total angular change. Away from the path the quotient
is already an integer, so the floor does not change its value. On the path
this is only a total extension; no winding interpretation is asserted there. -/
def windingNumber {n : ℕ} (p : Polygon Point2D n) (X : Point2D) : ℤ :=
  ⌊totalAngle p X / (2 * Real.pi)⌋

/-- An integer-valued signed crossing expression for computing winding. -/
def signedCrossings {n : ℕ} (p : Polygon Point2D n) (X : Point2D) : ℤ :=
  ∑ i : Fin n,
    let A := p i
    let B := p (finRotate n i)
    ((if X 1 < B 1 then 1 else 0) - (if X 1 < A 1 then 1 else 0)) *
      (if 0 < PolygonInterior.cross A B X * (B 1 - A 1) then 1 else 0)

theorem signedCrossings_cast {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    (signedCrossings p X : ℝ) =
      ∑ i : Fin n, PolygonInterior.edgeIndex (p i) (p (finRotate n i)) X := by
  simp only [signedCrossings, Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_ite,
    Int.cast_one, Int.cast_zero, PolygonInterior.edgeIndex, PolygonInterior.positive_eq, sub_pos]

/-- The signed crossing algorithm computes the full angular change, not
just its parity. The endpoint arguments telescope around the polygon. -/
theorem totalAngle_eq_signedCrossings {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    totalAngle p X = 2 * Real.pi * (signedCrossings p X : ℝ) := by
  have he (i : Fin n) : X ∉ segment (p i) (p (finRotate n i)) :=
    fun hi => hX ((mem_boundary_iff p X).mpr ⟨i, hi⟩)
  change (∑ i : Fin n,
    (PolygonWinding.vector (p (finRotate n i)) X / PolygonWinding.vector (p i) X).arg) = _
  simp_rw [PolygonWinding.arg_ratio_eq (he _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate n) (fun i => (-PolygonWinding.vector (p i) X).arg),
    sub_self, zero_add, ← Finset.mul_sum, signedCrossings_cast]

theorem windingNumber_eq_signedCrossings {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) : windingNumber p X = signedCrossings p X := by
  rw [windingNumber, totalAngle_eq_signedCrossings p hX,
    mul_div_cancel_left₀ _ (ne_of_gt Real.two_pi_pos), Int.floor_intCast]

/-- The angular expression is exactly integer-valued off the polygonal path. -/
theorem windingNumber_cast {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    (windingNumber p X : ℝ) = totalAngle p X / (2 * Real.pi) := by
  rw [windingNumber_eq_signedCrossings p hX, totalAngle_eq_signedCrossings p hX,
    mul_div_cancel_left₀ _ (ne_of_gt Real.two_pi_pos)]

/-- The continuously lifted argument of the polygon, starting at the argument
of its first vertex relative to `X`. -/
def argumentLift {n : ℕ} [NeZero n] (p : Polygon Point2D n) (X : Point2D)
    (hX : X ∉ p.boundary ℝ) :
    Path (PolygonWinding.vector (p 0) X).arg
      ((PolygonWinding.vector (p 0) X).arg + totalAngle p X) :=
  PolygonWinding.angleLiftChain n
    (fun i => PolygonWinding.vector (p (finRotate n i)) X / PolygonWinding.vector (p i) X)
    (fun i => PolygonWinding.ratio_mem_slitPlane
      (fun hi => hX ((mem_boundary_iff p X).mpr ⟨i, hi⟩)))
    (PolygonWinding.vector (p 0) X).arg

/-- The polygon's direction loop in the angle circle. Each lifted edge follows
the argument of the straight segment, as in `edgeAngleLift_projects`. -/
def argumentLoop {n : ℕ} [NeZero n] (p : Polygon Point2D n) (X : Point2D)
    (hX : X ∉ p.boundary ℝ) :
    Path ((PolygonWinding.vector (p 0) X).arg : Real.Angle)
      ((PolygonWinding.vector (p 0) X).arg : Real.Angle) :=
  ((argumentLift p X hX).map Real.Angle.continuous_coe).cast rfl (by
    rw [Real.Angle.coe_add, totalAngle_eq_signedCrossings p hX, mul_comm,
      Real.Angle.intCast_mul_eq_zsmul, Real.Angle.coe_two_pi, zsmul_zero, add_zero])

set_option backward.isDefEq.respectTransparency false in
/-- The angular-sum formula agrees with Mathlib's topological winding number,
defined through the fundamental group and continuous lifting of circle loops. -/
theorem windingNumber_eq_topological {n : ℕ} [NeZero n]
    (p : Polygon Point2D n) (X : Point2D) (hX : X ∉ p.boundary ℝ) :
    windingNumber p X = AddCircle.windingNumber (.of (.mk (argumentLoop p X hX))) := by
  apply Int.cast_injective (α := ℝ)
  rw [windingNumber_cast p hX]
  have he := AddCircle.windingNumber_eq_div (argumentLoop p X hX)
    (argumentLift p X hX).toContinuousMap (by rfl)
  convert he.symm using 1
  simp only [Path.coe_toContinuousMap, Path.source, Path.target, add_sub_cancel_left]

theorem oddEvenIndicator_eq_windingNumber {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    oddEvenIndicator p X = (1 - Real.cos ((windingNumber p X : ℝ) * Real.pi)) / 2 := by
  rw [oddEvenIndicator_eq_cos_indexSum, ← signedCrossings_cast,
    windingNumber_eq_signedCrossings p hX]

/-- Intrinsic odd–even membership: the winding number is odd. -/
theorem oddEvenIndicator_eq_one_iff_odd_windingNumber {n : ℕ}
    (p : Polygon Point2D n) {X : Point2D} (hX : X ∉ p.boundary ℝ) :
    oddEvenIndicator p X = 1 ↔ Odd (windingNumber p X) := by
  rw [oddEvenIndicator_eq_windingNumber p hX, Real.cos_int_mul_pi, neg_one_zpow_eq_ite]
  by_cases h : Even (windingNumber p X)
  · simp [h, ← Int.not_even_iff_odd]
  · simp [h, ← Int.not_even_iff_odd]

/-- The polygonal path together with the regions of odd winding number. -/
def windingFilledRegion {n : ℕ} (p : Polygon Point2D n) : Set Point2D :=
  p.boundary ℝ ∪ {X | X ∉ p.boundary ℝ ∧ Odd (windingNumber p X)}

theorem windingFilledRegion_eq_filledRegion {n : ℕ} (p : Polygon Point2D n) :
    windingFilledRegion p = filledRegion p := by
  ext X
  by_cases hX : X ∈ p.boundary ℝ
  · simp [windingFilledRegion, filledRegion, hX]
  · simp [windingFilledRegion, filledRegion, hX,
      oddEvenIndicator_eq_one_iff_odd_windingNumber p hX]

theorem mem_interior_iff_odd_windingNumber {n : ℕ}
    (p : Polygon Point2D n) {X : Point2D} (hX : X ∉ p.boundary ℝ) :
    X ∈ interior (windingFilledRegion p) ↔ Odd (windingNumber p X) := by
  rw [windingFilledRegion_eq_filledRegion, mem_interior_filledRegion_iff p hX,
    oddEvenIndicator_eq_one_iff_odd_windingNumber p hX]

/-- Interior membership is also characterized directly by Mathlib's
fundamental-group winding number of the polygon's direction loop. -/
theorem mem_interior_iff_odd_topologicalWinding {n : ℕ} [NeZero n]
    (p : Polygon Point2D n) (X : Point2D) (hX : X ∉ p.boundary ℝ) :
    X ∈ interior (windingFilledRegion p) ↔
      Odd (AddCircle.windingNumber (.of (.mk (argumentLoop p X hX)))) := by
  rw [mem_interior_iff_odd_windingNumber p hX, windingNumber_eq_topological p X hX]

/-- One counterclockwise turn around the origin. -/
theorem windingNumber_counterclockwise :
    windingNumber (ofVertices [!₂[1, 0], !₂[0, 1], !₂[-1, 0], !₂[0, -1]]) !₂[0, 0] = 1 := by
  simp only [windingNumber, totalAngle, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.sum_univ_succ, Complex.mk_eq_add_mul_I]
  field_simp
  norm_num

/-- Orientation reversal changes the integer sign. -/
theorem windingNumber_clockwise :
    windingNumber (ofVertices [!₂[1, 0], !₂[0, -1], !₂[-1, 0], !₂[0, 1]]) !₂[0, 0] = -1 := by
  simp only [windingNumber, totalAngle, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.sum_univ_succ, Complex.mk_eq_add_mul_I, Complex.arg_neg_I]
  convert (show ⌊(-1 : ℝ)⌋ = (-1 : ℤ) by norm_num) using 2
  field_simp
  rw [Complex.arg_neg_I]
  ring

/-- Two turns have winding two, although their odd–even interior is empty. -/
theorem windingNumber_double_traversal :
    windingNumber (ofVertices
      [!₂[1, 0], !₂[0, 1], !₂[-1, 0], !₂[0, -1],
       !₂[1, 0], !₂[0, 1], !₂[-1, 0], !₂[0, -1]]) !₂[0, 0] = 2 := by
  simp only [windingNumber, totalAngle, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.sum_univ_succ, Complex.mk_eq_add_mul_I]
  field_simp
  norm_num

end Polygon

end

end SympyGeometry
