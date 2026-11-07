module

public import SympyProofs.Geometry.Polygon
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Odd–even filling of polygonal paths

A horizontal ray to the right counts edges with exactly one endpoint strictly
above the query point. This half-open convention counts a shared vertex once
and ignores horizontal edges. The finite product below records the parity
using only real arithmetic and `Real.sign`, including at symbolic coordinates.
The filled set includes the complete polygonal path as well as the odd cells.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open Classical Filter Set
open scoped Topology

namespace PolygonInterior

/-- Indicator of strict positivity, expressed without a conditional. -/
def positive (x : ℝ) : ℝ := (Real.sign x ^ 2 + Real.sign x) / 2

theorem positive_eq (x : ℝ) : positive x = if 0 < x then 1 else 0 := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [positive, Real.sign_of_neg h, not_lt.mpr h.le]
  · norm_num [positive]
  · simp [positive, Real.sign_of_pos h, h]

theorem positive_cases (x : ℝ) : positive x = 0 ∨ positive x = 1 := by
  rw [positive_eq]; split_ifs <;> simp

/-- The oriented determinant of the two endpoint vectors based at `X`. -/
def cross (A B X : Point2D) : ℝ :=
  (A 0 - X 0) * (B 1 - X 1) - (A 1 - X 1) * (B 0 - X 0)

/-- One precisely when the half-open edge crosses the horizontal right ray. -/
def edgeCrossing (A B X : Point2D) : ℝ :=
  (positive (A 1 - X 1) - positive (B 1 - X 1)) ^ 2 *
    positive (cross A B X * (B 1 - A 1))

/-- The same ray crossing, with upward/downward orientation. -/
def edgeIndex (A B X : Point2D) : ℝ :=
  (positive (B 1 - X 1) - positive (A 1 - X 1)) *
    positive (cross A B X * (B 1 - A 1))

/-- A precise half-open ray-crossing predicate. -/
def CrossesRay (A B X : Point2D) : Prop :=
  ((A 1 ≤ X 1 ∧ X 1 < B 1) ∨ (B 1 ≤ X 1 ∧ X 1 < A 1)) ∧
    0 < cross A B X * (B 1 - A 1)

theorem edgeCrossing_eq (A B X : Point2D) :
    edgeCrossing A B X = if CrossesRay A B X then 1 else 0 := by
  unfold edgeCrossing CrossesRay
  simp only [positive_eq, sub_pos]
  split_ifs <;> norm_num at * <;> grind

/-- The determinant test really is intersection with the horizontal ray to
the right. The endpoint-height condition supplies the half-open convention. -/
theorem crossesRay_iff (A B X : Point2D) :
    CrossesRay A B X ↔
      ((A 1 ≤ X 1 ∧ X 1 < B 1) ∨ (B 1 ≤ X 1 ∧ X 1 < A 1)) ∧
        ∃ Y ∈ segment A B, Y 1 = X 1 ∧ X 0 < Y 0 := by
  have hdet {Y : Point2D} (hY : Y ∈ segment A B) (hy : Y 1 = X 1) :
      cross A B X = (Y 0 - X 0) * (B 1 - A 1) := by
    obtain ⟨t, _, rfl⟩ := hY
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hy ⊢
    unfold cross
    linear_combination -(B 0 - A 0) * hy
  have hpoint (h : (A 1 ≤ X 1 ∧ X 1 < B 1) ∨ (B 1 ≤ X 1 ∧ X 1 < A 1)) :
      ∃ Y ∈ segment A B, Y 1 = X 1 := by
    have hc : ContinuousOn (fun t : ℝ => (1 - t) * A 1 + t * B 1) (Set.Icc 0 1) :=
      (by fun_prop : Continuous (fun t : ℝ => (1 - t) * A 1 + t * B 1)).continuousOn
    rcases h with h | h
    · obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
        (show X 1 ∈ Set.Icc ((1 - 0) * A 1 + 0 * B 1) ((1 - 1) * A 1 + 1 * B 1) by
          simpa using And.intro h.1 h.2.le)
      exact ⟨(1 - t) • A + t • B, ⟨t, ht, rfl⟩, he⟩
    · obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
        (show X 1 ∈ Set.Icc ((1 - 1) * A 1 + 1 * B 1) ((1 - 0) * A 1 + 0 * B 1) by
          simpa using And.intro h.1 h.2.le)
      exact ⟨(1 - t) • A + t • B, ⟨t, ht, rfl⟩, he⟩
  constructor
  · rintro ⟨h, hc⟩
    obtain ⟨Y, hY, hy⟩ := hpoint h
    refine ⟨h, Y, hY, hy, ?_⟩
    rw [hdet hY hy] at hc
    have hprod : 0 < (Y 0 - X 0) * (B 1 - A 1) ^ 2 := by nlinarith [hc]
    exact sub_pos.mp ((mul_pos_iff.mp hprod).resolve_right
      (fun hh => (sq_nonneg (B 1 - A 1)).not_gt hh.2)).1
  · rintro ⟨h, Y, hY, hy, hx⟩
    refine ⟨h, ?_⟩
    have hd : B 1 - A 1 ≠ 0 := by rcases h with h | h <;> linarith
    rw [hdet hY hy]
    nlinarith [mul_pos (sub_pos.mpr hx) (sq_pos_of_ne_zero hd)]

private theorem edge_trig (A B X : Point2D) :
    Real.cos (edgeIndex A B X * Real.pi) = 1 - 2 * edgeCrossing A B X ∧
    Real.sin (edgeIndex A B X * Real.pi) = 0 := by
  unfold edgeIndex edgeCrossing
  rcases positive_cases (A 1 - X 1) with hA | hA <;>
    rcases positive_cases (B 1 - X 1) with hB | hB <;>
    rcases positive_cases (cross A B X * (B 1 - A 1)) with hC | hC <;>
    norm_num [hA, hB, hC]

private theorem product_eq_cos_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (h : ∀ i ∈ s, Real.cos (a i * Real.pi) = b i ∧ Real.sin (a i * Real.pi) = 0) :
    Real.cos ((∑ i ∈ s, a i) * Real.pi) = ∏ i ∈ s, b i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, add_mul, Real.cos_add,
      (h i (Finset.mem_insert_self _ _)).1, (h i (Finset.mem_insert_self _ _)).2,
      zero_mul, sub_zero, ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

private theorem mem_segment_of_cross_zero {A B X : Point2D} (k : Fin 2)
    (hab : A k < B k) (ha : A k ≤ X k) (hb : X k ≤ B k)
    (hc : cross A B X = 0) : X ∈ segment A B := by
  have hd : 0 < B k - A k := sub_pos.mpr hab
  refine ⟨(X k - A k) / (B k - A k),
    ⟨div_nonneg (sub_nonneg.mpr ha) hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  ext l
  fin_cases k <;> fin_cases l <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    dsimp at * <;> field_simp <;> unfold cross at hc <;> nlinarith

private theorem cross_swap (A B X : Point2D) : cross B A X = -cross A B X := by
  unfold cross; ring

private theorem positive_y_eq_of_cross_zero {A B X : Point2D}
    (hX : X ∉ segment A B) (hc : cross A B X = 0) :
    positive (A 1 - X 1) = positive (B 1 - X 1) := by
  simp only [positive_eq, sub_pos]
  split_ifs with ha hb hb
  · rfl
  · exfalso
    have hm := mem_segment_of_cross_zero 1 (lt_of_le_of_lt (le_of_not_gt hb) ha)
      (le_of_not_gt hb) ha.le (by rw [cross_swap, hc, neg_zero])
    apply hX
    rcases hm with ⟨t, ht, he⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by
      simpa [sub_sub_cancel, add_comm] using he⟩
  · exact False.elim (hX (mem_segment_of_cross_zero 1
      (lt_of_le_of_lt (le_of_not_gt ha) hb) (le_of_not_gt ha) hb.le hc))
  · rfl

private theorem eventually_sign_eq {f : Point2D → ℝ} {X : Point2D}
    (hf : ContinuousAt f X) (hne : f X ≠ 0) :
    ∀ᶠ Y in 𝓝 X, Real.sign (f Y) = Real.sign (f X) := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hf.eventually (gt_mem_nhds h)] with Y hY
    rw [Real.sign_of_neg hY, Real.sign_of_neg h]
  · filter_upwards [hf.eventually (lt_mem_nhds h)] with Y hY
    rw [Real.sign_of_pos hY, Real.sign_of_pos h]

private theorem eventually_positive_eq {f : Point2D → ℝ} {X : Point2D}
    (hf : ContinuousAt f X) (hne : f X ≠ 0) :
    ∀ᶠ Y in 𝓝 X, positive (f Y) = positive (f X) := by
  filter_upwards [eventually_sign_eq hf hne] with Y hY
  simp only [positive, hY]

private def binarySign (x : ℝ) : ℝ := 2 * positive x - 1

private def edgeWeight (A B X : Point2D) : ℝ :=
  |binarySign (A 1 - X 1) - binarySign (B 1 - X 1)| * Real.sign (cross A B X)

private def vertexCorrection (A X Y : Point2D) : ℝ :=
  if A 1 = X 1 then Real.sign (A 0 - X 0) *
    (binarySign (A 1 - Y 1) - binarySign (A 1 - X 1)) else 0

private theorem crossing_weight_identity (a b d : ℝ)
    (hz : d = 0 → positive a = positive b) :
    4 * ((positive b - positive a) * positive (d * (b - a))) =
      binarySign b - binarySign a + |binarySign a - binarySign b| * Real.sign d := by
  by_cases ha : 0 < a <;> by_cases hb : 0 < b
  · simp [binarySign, positive_eq, ha, hb]
  · have hba : b - a < 0 := by linarith
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · norm_num [binarySign, positive_eq, ha, hb, Real.sign_of_neg hd,
        mul_pos_of_neg_of_neg hd hba]
    · have := hz rfl
      simp [positive_eq, ha, hb] at this
    · norm_num [binarySign, positive_eq, ha, hb, Real.sign_of_pos hd,
        not_lt.mpr (mul_neg_of_pos_of_neg hd hba).le]
  · have hba : 0 < b - a := by linarith
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · norm_num [binarySign, positive_eq, ha, hb, Real.sign_of_neg hd,
        not_lt.mpr (mul_neg_of_neg_of_pos hd hba).le]
    · have := hz rfl
      simp [positive_eq, ha, hb] at this
    · norm_num [binarySign, positive_eq, ha, hb, Real.sign_of_pos hd, mul_pos hd hba]
  · simp [binarySign, positive_eq, ha, hb]

private theorem edgeIndex_eq_weight {A B X : Point2D} (hX : X ∉ segment A B) :
    4 * edgeIndex A B X = binarySign (B 1 - X 1) - binarySign (A 1 - X 1) +
      edgeWeight A B X := by
  have h := crossing_weight_identity (A 1 - X 1) (B 1 - X 1) (cross A B X)
    (positive_y_eq_of_cross_zero hX)
  simpa only [edgeIndex, edgeWeight, sub_sub_sub_cancel_right] using h

private theorem not_mem_segment_swap {A B X : Point2D} (hX : X ∉ segment A B) :
    X ∉ segment B A := by
  rintro ⟨t, ht, he⟩
  exact hX ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    by simpa [sub_sub_cancel, add_comm] using he⟩

private theorem x_ne_of_y_eq {A B X : Point2D} (hX : X ∉ segment A B)
    (hy : A 1 = X 1) : A 0 - X 0 ≠ 0 := by
  intro hx
  have hAX : A = X := by ext k; fin_cases k; exact sub_eq_zero.mp hx; exact hy
  apply hX
  exact ⟨0, by norm_num, by simpa using hAX⟩

private theorem horizontal_sign_eq {A B X : Point2D} (hX : X ∉ segment A B)
    (ha : A 1 = X 1) (hb : B 1 = X 1) :
    Real.sign (A 0 - X 0) = Real.sign (B 0 - X 0) := by
  have hc : cross A B X = 0 := by simp [cross, ha, hb]
  rcases lt_or_gt_of_ne (x_ne_of_y_eq hX ha) with hax | hax <;>
    rcases lt_or_gt_of_ne (x_ne_of_y_eq (not_mem_segment_swap hX) hb) with hbx | hbx
  · rw [Real.sign_of_neg hax, Real.sign_of_neg hbx]
  · exact False.elim (hX (mem_segment_of_cross_zero 0 (by linarith) (by linarith)
      (by linarith) hc))
  · exact False.elim (not_mem_segment_swap hX (mem_segment_of_cross_zero 0
      (by linarith) (by linarith) (by linarith) (by rw [cross_swap, hc, neg_zero])))
  · rw [Real.sign_of_pos hax, Real.sign_of_pos hbx]

private theorem edgeWeight_swap (A B X : Point2D) :
    edgeWeight B A X = -edgeWeight A B X := by
  unfold edgeWeight
  rw [cross_swap A B X, Real.sign_neg, abs_sub_comm, mul_neg]

private theorem sign_mul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;>
    rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb),
      Real.sign_of_neg ha, Real.sign_of_neg hb]; norm_num
  · simp
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb),
      Real.sign_of_neg ha, Real.sign_of_pos hb]; norm_num
  · simp
  · simp
  · simp
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb),
      Real.sign_of_pos ha, Real.sign_of_neg hb]; norm_num
  · simp
  · rw [Real.sign_of_pos (mul_pos ha hb), Real.sign_of_pos ha, Real.sign_of_pos hb]; norm_num

private theorem binarySign_eq_sign {x : ℝ} (hx : x ≠ 0) : binarySign x = Real.sign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · norm_num [binarySign, positive_eq, not_lt.mpr h.le, Real.sign_of_neg h]
  · norm_num [binarySign, positive_eq, h, Real.sign_of_pos h]

private theorem weight_endpoint_algebra (u v c : ℝ) :
    |binarySign u - binarySign v| * (c * binarySign v) =
      c * (binarySign v - binarySign u) := by
  rcases positive_cases u with hu | hu <;> rcases positive_cases v with hv | hv <;>
    norm_num [binarySign, hu, hv] <;> ring

/-- At a vertex's height, the possible jump is a correction attached to that
vertex. Adjacent edges receive opposite corrections, so their sum cancels. -/
private theorem weight_near_endpoint {A B X : Point2D} (hX : X ∉ segment A B)
    (ha : A 1 = X 1) (hb : B 1 ≠ X 1) :
    ∀ᶠ Y in 𝓝 X, edgeWeight A B Y = edgeWeight A B X +
      vertexCorrection B X Y - vertexCorrection A X Y := by
  have hx := x_ne_of_y_eq hX ha
  have hc : cross A B X = (A 0 - X 0) * (B 1 - X 1) := by simp [cross, ha]
  have hcn : cross A B X ≠ 0 := by rw [hc]; exact mul_ne_zero hx (sub_ne_zero.mpr hb)
  have hbc := eventually_positive_eq
    (show ContinuousAt (fun Y : Point2D => B 1 - Y 1) X by fun_prop) (sub_ne_zero.mpr hb)
  have hcc := eventually_sign_eq
    (show ContinuousAt (cross A B) X by unfold cross; fun_prop) hcn
  filter_upwards [hbc, hcc] with Y hby hcy
  have hbs : binarySign (B 1 - Y 1) = binarySign (B 1 - X 1) := by
    simp only [binarySign, hby]
  have hcs : Real.sign (cross A B X) =
      Real.sign (A 0 - X 0) * binarySign (B 1 - X 1) := by
    rw [hc, sign_mul, binarySign_eq_sign (sub_ne_zero.mpr hb)]
  simp only [edgeWeight, hbs, hcy, hcs, weight_endpoint_algebra,
    vertexCorrection, ite_eq_left ha, ite_eq_right hb]
  ring

private theorem weight_locally_corrected {A B X : Point2D} (hX : X ∉ segment A B) :
    ∀ᶠ Y in 𝓝 X, edgeWeight A B Y = edgeWeight A B X +
      vertexCorrection B X Y - vertexCorrection A X Y := by
  by_cases ha : A 1 = X 1
  · by_cases hb : B 1 = X 1
    · have hs := horizontal_sign_eq hX ha hb
      exact Filter.Eventually.of_forall fun Y => by
        simp [edgeWeight, vertexCorrection, ha, hb, hs]
    · exact weight_near_endpoint hX ha hb
  · by_cases hb : B 1 = X 1
    · filter_upwards [weight_near_endpoint (not_mem_segment_swap hX) hb ha] with Y hY
      rw [edgeWeight_swap A B Y, edgeWeight_swap A B X] at hY
      linarith
    · have hea := eventually_positive_eq
        (show ContinuousAt (fun Y : Point2D => A 1 - Y 1) X by fun_prop) (sub_ne_zero.mpr ha)
      have heb := eventually_positive_eq
        (show ContinuousAt (fun Y : Point2D => B 1 - Y 1) X by fun_prop) (sub_ne_zero.mpr hb)
      by_cases hc : cross A B X = 0
      · have hab := positive_y_eq_of_cross_zero hX hc
        filter_upwards [hea, heb] with Y hya hyb
        simp [edgeWeight, binarySign, hya, hyb, hab, vertexCorrection, ha, hb]
      · have hec := eventually_sign_eq
          (show ContinuousAt (cross A B) X by unfold cross; fun_prop) hc
        filter_upwards [hea, heb, hec] with Y hya hyb hyc
        simp [edgeWeight, binarySign, hya, hyb, hyc, vertexCorrection, ha, hb]

private theorem index_sum_eq_weight_sum {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    4 * ∑ i : Fin n, edgeIndex (p i) (p (finRotate n i)) X =
      ∑ i : Fin n, edgeWeight (p i) (p (finRotate n i)) X := by
  rw [Finset.mul_sum]
  have he (i : Fin n) : X ∉ segment (p i) (p (finRotate n i)) :=
    fun hi => hX ((Polygon.mem_boundary_iff p X).mpr ⟨i, hi⟩)
  simp_rw [edgeIndex_eq_weight (he _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate n) (fun i => binarySign (p i 1 - X 1))]
  ring

private theorem weight_sum_locally_constant {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    ∀ᶠ Y in 𝓝 X,
      (∑ i : Fin n, edgeWeight (p i) (p (finRotate n i)) Y) =
        ∑ i : Fin n, edgeWeight (p i) (p (finRotate n i)) X := by
  have he (i : Fin n) : ∀ᶠ Y in 𝓝 X,
      edgeWeight (p i) (p (finRotate n i)) Y =
        edgeWeight (p i) (p (finRotate n i)) X +
          vertexCorrection (p (finRotate n i)) X Y - vertexCorrection (p i) X Y :=
    weight_locally_corrected (fun hi => hX ((Polygon.mem_boundary_iff p X).mpr ⟨i, hi⟩))
  filter_upwards [Filter.eventually_all.mpr he] with Y hY
  simp_rw [hY, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Equiv.sum_comp (finRotate n) (fun i => vertexCorrection (p i) X Y)]
  ring

end PolygonInterior

namespace Polygon

theorem isCompact_boundary {n : ℕ} (p : Polygon Point2D n) : IsCompact (p.boundary ℝ) := by
  apply isCompact_iUnion
  intro i
  rw [edgeSet_eq_segment]
  exact isCompact_Icc.image (by fun_prop)

theorem isPreconnected_boundary {n : ℕ} [NeZero n] (p : Polygon Point2D n) :
    IsPreconnected (p.boundary ℝ) := by
  apply IsPreconnected.iUnion_of_reflTransGen
  · intro i
    rw [edgeSet_eq_segment]
    exact isPreconnected_Icc.image _ (by fun_prop)
  · intro i j
    have hstep (k : Fin n) :
        (p.edgeSet ℝ k ∩ p.edgeSet ℝ (k + 1)).Nonempty := by
      refine ⟨p (k + 1), ?_, ?_⟩ <;> rw [edgeSet_eq_segment]
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨0, by norm_num, by simp⟩
    have hpath (k : ℕ) : Relation.ReflTransGen
        (fun i j => (p.edgeSet ℝ i ∩ p.edgeSet ℝ j).Nonempty) i (i + Fin.ofNat n k) := by
      induction k with
      | zero => simpa using Relation.ReflTransGen.refl (a := i)
      | succ k ih =>
        have he : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
          ext; simp [Fin.val_add, Nat.add_mod]
        simpa only [he, add_assoc] using ih.tail (hstep (i + Fin.ofNat n k))
    simpa using hpath (j - i).val

/-- Odd–even interior parity. On the path itself the half-open convention
still returns zero or one; membership in `filledRegion` always includes it. -/
def oddEvenIndicator {n : ℕ} (p : Polygon Point2D n) (X : Point2D) : ℝ :=
  let positive := fun x : ℝ => (Real.sign x ^ 2 + Real.sign x) / 2
  let parity := ∏ i : Fin n,
    let A := p i
    let B := p (finRotate n i)
    let a := A 1 - X 1
    let b := B 1 - X 1
    let det := (A 0 - X 0) * b - a * (B 0 - X 0)
    let crossing := (positive a - positive b) ^ 2 * positive (det * (B 1 - A 1))
    1 - 2 * crossing
  (1 - parity) / 2

/-- The path together with all cells selected by odd crossing parity. -/
def filledRegion {n : ℕ} (p : Polygon Point2D n) : Set Point2D :=
  p.boundary ℝ ∪ {X | oddEvenIndicator p X = 1}

theorem boundary_subset_filledRegion {n : ℕ} (p : Polygon Point2D n) :
    p.boundary ℝ ⊆ filledRegion p := fun _ h => Or.inl h

theorem oddEvenIndicator_eq_product {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    oddEvenIndicator p X =
      (1 - ∏ i : Fin n, (1 - 2 * PolygonInterior.edgeCrossing
        (p i) (p (finRotate n i)) X)) / 2 := rfl

/-- The parity product also equals the cosine of the signed crossing sum. -/
theorem oddEvenIndicator_eq_cos_indexSum {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    oddEvenIndicator p X =
      (1 - Real.cos ((∑ i : Fin n,
        PolygonInterior.edgeIndex (p i) (p (finRotate n i)) X) * Real.pi)) / 2 := by
  rw [oddEvenIndicator_eq_product, PolygonInterior.product_eq_cos_sum Finset.univ
    (fun i : Fin n => PolygonInterior.edgeIndex (p i) (p (finRotate n i)) X)
    (fun i : Fin n => 1 - 2 * PolygonInterior.edgeCrossing (p i) (p (finRotate n i)) X)
    (fun i _ => PolygonInterior.edge_trig (p i) (p (finRotate n i)) X)]

/-- The product is exactly the usual odd–even ray-count rule. -/
theorem oddEvenIndicator_eq_count {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    oddEvenIndicator p X =
      (1 - (-1 : ℝ) ^ (Finset.univ.filter (fun i : Fin n =>
        PolygonInterior.CrossesRay (p i) (p (finRotate n i)) X)).card) / 2 := by
  rw [oddEvenIndicator_eq_product]
  congr 2
  simp_rw [PolygonInterior.edgeCrossing_eq]
  simp only [mul_ite, mul_one, mul_zero, sub_ite]
  norm_num
  rw [Finset.prod_ite]
  simp

theorem oddEvenIndicator_cases {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    oddEvenIndicator p X = 0 ∨ oddEvenIndicator p X = 1 := by
  rw [oddEvenIndicator_eq_count]
  rcases neg_one_pow_eq_or ℝ (Finset.univ.filter (fun i : Fin n =>
    PolygonInterior.CrossesRay (p i) (p (finRotate n i)) X)).card with h | h <;> rw [h] <;> norm_num

theorem oddEvenIndicator_eq_one_iff {n : ℕ} (p : Polygon Point2D n) (X : Point2D) :
    oddEvenIndicator p X = 1 ↔ Odd (Finset.univ.filter (fun i : Fin n =>
      PolygonInterior.CrossesRay (p i) (p (finRotate n i)) X)).card := by
  rw [oddEvenIndicator_eq_count, ← neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)]
  constructor <;> intro h <;> linarith

/-- Away from the polygonal path, crossing parity is locally constant. This
includes query points level with vertices and horizontal edges. -/
theorem oddEvenIndicator_locally_constant {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    ∀ᶠ Y in 𝓝 X, oddEvenIndicator p Y = oddEvenIndicator p X := by
  have hn : ∀ᶠ Y in 𝓝 X, Y ∉ p.boundary ℝ :=
    (isCompact_boundary p).isClosed.isOpen_compl.mem_nhds hX
  filter_upwards [hn, PolygonInterior.weight_sum_locally_constant p hX] with Y hY he
  have hi : (∑ i : Fin n, PolygonInterior.edgeIndex (p i) (p (finRotate n i)) Y) =
      ∑ i : Fin n, PolygonInterior.edgeIndex (p i) (p (finRotate n i)) X := by
    have hx := PolygonInterior.index_sum_eq_weight_sum p hX
    have hy := PolygonInterior.index_sum_eq_weight_sum p hY
    linarith
  have hcos (Z : Point2D) := PolygonInterior.product_eq_cos_sum Finset.univ
    (fun i : Fin n => PolygonInterior.edgeIndex (p i) (p (finRotate n i)) Z)
    (fun i : Fin n => 1 - 2 * PolygonInterior.edgeCrossing (p i) (p (finRotate n i)) Z)
    (fun i _ => PolygonInterior.edge_trig (p i) (p (finRotate n i)) Z)
  rw [oddEvenIndicator_eq_product, oddEvenIndicator_eq_product, ← hcos Y, ← hcos X, hi]

theorem isClosed_filledRegion {n : ℕ} (p : Polygon Point2D n) : IsClosed (filledRegion p) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro X hX
  have hb : X ∉ p.boundary ℝ := fun h => hX (Or.inl h)
  have hi : oddEvenIndicator p X ≠ 1 := fun h => hX (Or.inr h)
  filter_upwards [(isCompact_boundary p).isClosed.isOpen_compl.mem_nhds hb,
    oddEvenIndicator_locally_constant p hb] with Y hY he
  rintro (h | h)
  · exact hY h
  · exact hi (he ▸ h)

/-- The odd–even filled region has no frontier away from the input path. -/
theorem frontier_filledRegion_subset {n : ℕ} (p : Polygon Point2D n) :
    frontier (filledRegion p) ⊆ p.boundary ℝ := by
  intro X hX
  by_contra hb
  have hi : oddEvenIndicator p X = 1 :=
    ((isClosed_filledRegion p).frontier_subset hX).resolve_left hb
  have hn : filledRegion p ∈ 𝓝 X := by
    filter_upwards [oddEvenIndicator_locally_constant p hb] with Y he
    exact Or.inr (he.trans hi)
  exact hX.2 (mem_interior_iff_mem_nhds.mpr hn)

/-- A point above every vertex is outside both the path and the odd cells. -/
theorem not_mem_filledRegion_of_above {n : ℕ} (p : Polygon Point2D n) (X : Point2D)
    (h : ∀ i, p i 1 < X 1) : X ∉ filledRegion p := by
  have hb : X ∉ p.boundary ℝ := by
    rintro hX
    obtain ⟨i, t, ht, he⟩ := (mem_boundary_iff p X).mp hX
    have hc := congrArg (fun Z : Point2D => Z 1) he
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hc
    have hi := h i
    have hj := h (finRotate n i)
    have hpos : 0 < (1 - t) * (X 1 - p i 1) + t * (X 1 - p (finRotate n i) 1) := by
      by_cases hz : t = 0
      · simp [hz, sub_pos.mpr hi]
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (by linarith [ht.2]) (by linarith))
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) (by linarith))
    nlinarith
  have hi : oddEvenIndicator p X = 0 := by
    rw [oddEvenIndicator_eq_product]
    have hz (i : Fin n) : PolygonInterior.edgeCrossing (p i) (p (finRotate n i)) X = 0 := by
      simp only [PolygonInterior.edgeCrossing, PolygonInterior.positive_eq,
        not_lt.mpr (sub_nonpos.mpr (h i).le),
        not_lt.mpr (sub_nonpos.mpr (h (finRotate n i)).le), ite_false,
        sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    simp only [hz, mul_zero, sub_zero, Finset.prod_const_one, sub_self, zero_div]
  rintro (h | h)
  · exact hb h
  · change oddEvenIndicator p X = 1 at h
    rw [hi] at h; norm_num at h

theorem filledRegion_ne_univ {n : ℕ} (p : Polygon Point2D n) : filledRegion p ≠ Set.univ := by
  let H : ℝ := (∑ i : Fin n, |p i 1|) + 1
  have hH (i : Fin n) : p i 1 < H := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (p j 1))
      (Finset.mem_univ i)
    dsimp [H]
    linarith [le_abs_self (p i 1)]
  intro he
  exact not_mem_filledRegion_of_above p !₂[0, H] hH (he ▸ Set.mem_univ _)

/-- Off the path, odd parity is exactly topological interior membership. -/
theorem mem_interior_filledRegion_iff {n : ℕ} (p : Polygon Point2D n) {X : Point2D}
    (hX : X ∉ p.boundary ℝ) :
    X ∈ interior (filledRegion p) ↔ oddEvenIndicator p X = 1 := by
  constructor
  · intro h
    exact (interior_subset h).resolve_left hX
  · intro h
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [oddEvenIndicator_locally_constant p hX] with Y hY
    exact Or.inr (hY.trans h)

/-- A concave notch is outside, even though it lies in the convex hull. -/
theorem oddEvenIndicator_concave_notch :
    oddEvenIndicator (ofVertices
      [!₂[0, 0], !₂[4, 0], !₂[4, 1], !₂[1, 1], !₂[1, 4], !₂[0, 4]]) !₂[2, 2] = 0 := by
  simp only [oddEvenIndicator, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.prod_univ_succ, Real.sign]

/-- A point level with a concave vertex can still be strictly inside. -/
theorem oddEvenIndicator_vertex_height :
    oddEvenIndicator (ofVertices
      [!₂[0, 0], !₂[4, 0], !₂[4, 1], !₂[1, 1], !₂[1, 4], !₂[0, 4]]) !₂[1 / 2, 1] = 1 := by
  simp only [oddEvenIndicator, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.prod_univ_succ, Real.sign]

/-- The lower lobe of a self-intersecting bow tie is filled. -/
theorem oddEvenIndicator_bowtie_lobe :
    oddEvenIndicator (ofVertices
      [!₂[0, 0], !₂[4, 4], !₂[0, 4], !₂[4, 0]]) !₂[2, 1 / 2] = 1 := by
  simp only [oddEvenIndicator, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.prod_univ_succ, Real.sign]

/-- Traversing a square twice cancels its interior under odd–even filling.
This distinguishes the convention from nonzero-winding filling. -/
theorem oddEvenIndicator_double_traversal :
    oddEvenIndicator (ofVertices
      [!₂[0, 0], !₂[4, 0], !₂[4, 4], !₂[0, 4],
       !₂[0, 0], !₂[4, 0], !₂[4, 4], !₂[0, 4]]) !₂[1, 1] = 0 := by
  simp only [oddEvenIndicator, ofVertices, List.length_cons, List.length_nil]
  norm_num [Fin.prod_univ_succ, Real.sign]

end Polygon

end

end SympyGeometry
