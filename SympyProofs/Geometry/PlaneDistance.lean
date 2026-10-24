module

public import SympyProofs.Geometry.Basic
public import SympyProofs.Geometry.ScalarDistance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Euclidean distances from planes to segments, rays, lines, and other planes

For `plane P n`, `segment A B`, `ray A B`, and `line A B`, write
`a = ⟪n, A - P⟫`, `b = ⟪n, B - P⟫`, `c = ⟪n, B - A⟫`, and
`N = Real.sqrt ⟪n, n⟫ = ‖n‖`. The distance theorems use local `let`
bindings for these quantities, with `c = b - a`.
The segment distance is `(|a| + |b| - |c|) / (2 * N)`.
The ray distance is `|a| * (1 + min 0 (Real.sign (a * c))) / N`.
The line distance is `|a| * (1 - |Real.sign c|) / N`.
For a second plane `plane Q m`, put
`Δ = ⟪n, n⟫ * ⟪m, m⟫ - ⟪n, m⟫ ^ 2`. The plane-to-plane distance is
`|⟪n, Q - P⟫| * (1 - Real.sign Δ) / N`: `Δ` vanishes for parallel normals
and is positive otherwise.

Planes, segments, rays, and lines use the set-based definitions in `SympyGeometry`.
Each plane's normal is assumed nonzero, so that it defines a proper plane.
No hypothesis excludes parallelism, containment, or coincident defining points
for a segment, ray, or line. We prove these formulas for the infimum of actual pairwise
Euclidean distances and exhibit a closest pair.
The results hold in any real inner product space, in particular
`EuclideanSpace ℝ (Fin 3)`.
-/

@[expose] public section

namespace SympyGeometry

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The infimum of pairwise Euclidean distances. The theorems below also prove
attainment, so no empty-set convention is used in their conclusions. -/
noncomputable def distance (S T : Set E) : ℝ :=
  sInf {r | ∃ x ∈ S, ∃ y ∈ T, dist x y = r}

/-- Cauchy--Schwarz gives a lower bound for the distance to every point of the plane. -/
theorem residual_div_norm_le_dist (P n : E) (hn : n ≠ 0)
    (x y : E) (hy : y ∈ plane P n) :
    |⟪n, x - P⟫_ℝ| / ‖n‖ ≤ dist x y := by
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  have h := abs_real_inner_le_norm n (x - y)
  rw [inner_sub_right, (mem_plane_iff_inner_eq P n y).mp hy] at h
  simpa only [inner_sub_right, dist_eq_norm, mul_comm] using h

/-- Orthogonal projection onto the plane. -/
noncomputable def planeProjection (P n x : E) : E :=
  x - (⟪n, x - P⟫_ℝ / ‖n‖ ^ 2) • n

theorem planeProjection_mem (P n : E) (hn : n ≠ 0) (x : E) :
    planeProjection P n x ∈ plane P n := by
  have hnorm : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  rw [mem_plane_iff_inner_eq]
  change ⟪n, x - (⟪n, x - P⟫_ℝ / ‖n‖ ^ 2) • n⟫_ℝ = ⟪n, P⟫_ℝ
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ hnorm, inner_sub_right]
  ring

theorem dist_planeProjection (P n : E) (hn : n ≠ 0) (x : E) :
    dist x (planeProjection P n x) = |⟪n, x - P⟫_ℝ| / ‖n‖ := by
  have hnorm : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  rw [dist_eq_norm, planeProjection, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
    abs_div, abs_of_nonneg (sq_nonneg ‖n‖)]
  field_simp

/-- The usual point-to-plane formula, stated using mathlib's metric distance to a set. -/
theorem infDist_plane (P n : E) (hn : n ≠ 0) (x : E) :
    Metric.infDist x (plane P n) = |⟪n, x - P⟫_ℝ| / ‖n‖ := by
  have hp := planeProjection_mem P n hn x
  apply le_antisymm
  · calc
      _ ≤ dist x (planeProjection P n x) := Metric.infDist_le_dist_of_mem hp
      _ = _ := dist_planeProjection P n hn x
  · exact (Metric.le_infDist ⟨_, hp⟩).mpr fun y hy =>
      residual_div_norm_le_dist P n hn x y hy

/-- Lift an attained scalar minimum to a closest pair in Euclidean geometry. -/
theorem plane_distance_isLeast_of_residual (P n : E) (hn : n ≠ 0)
    (S : Set E) (m : ℝ)
    (hlower : ∀ x ∈ S, m ≤ |⟪n, x - P⟫_ℝ|)
    (hattain : ∃ x ∈ S, |⟪n, x - P⟫_ℝ| = m) :
    IsLeast {r | ∃ x ∈ S, ∃ y ∈ plane P n, dist x y = r} (m / ‖n‖) := by
  constructor
  · obtain ⟨x, hx, he⟩ := hattain
    exact ⟨x, hx, planeProjection P n x, planeProjection_mem P n hn x,
      by rw [dist_planeProjection P n hn x, he]⟩
  · rintro r ⟨x, hx, y, hy, rfl⟩
    calc
      m / ‖n‖ ≤ |⟪n, x - P⟫_ℝ| / ‖n‖ :=
        div_le_div_of_nonneg_right (hlower x hx) (norm_nonneg n)
      _ ≤ dist x y := residual_div_norm_le_dist P n hn x y hy

theorem segment_residual (P n A B : E) (t : ℝ) :
    ⟪n, (1 - t) • A + t • B - P⟫_ℝ =
      (1 - t) * ⟪n, A - P⟫_ℝ + t * ⟪n, B - P⟫_ℝ := by
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
  ring

theorem ray_residual (P n A B : E) (t : ℝ) :
    ⟪n, A + t • (B - A) - P⟫_ℝ = ⟪n, A - P⟫_ℝ + t * ⟪n, B - A⟫_ℝ := by
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
  ring

theorem line_residual (P n A B : E) (t : ℝ) :
    ⟪n, A + t • (B - A) - P⟫_ℝ = ⟪n, A - P⟫_ℝ + t * ⟪n, B - A⟫_ℝ :=
  ray_residual P n A B t

/-- Both a global lower bound and existence of a closest segment/plane pair. -/
theorem segment_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    IsLeast {r | ∃ x ∈ segment A B, ∃ y ∈ plane P n, dist x y = r}
      (segmentValue ⟪n, A - P⟫_ℝ ⟪n, B - P⟫_ℝ / ‖n‖) := by
  rw [segment_eq_image]
  apply plane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, ht, rfl⟩
    rw [segment_residual]
    exact segmentValue_le _ _ t ht
  · obtain ⟨t, ht, he⟩ := segmentValue_attained ⟪n, A - P⟫_ℝ ⟪n, B - P⟫_ℝ
    exact ⟨_, ⟨t, ht, rfl⟩, by rw [segment_residual, he]⟩

/-- Segment distance as an expression with absolute values; parallelism needs no test. -/
theorem segment_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℝ
    let b := ⟪n, B - P⟫_ℝ
    let c := ⟪n, B - A⟫_ℝ
    let N := Real.sqrt ⟪n, n⟫_ℝ
    distance (segment A B) (plane P n) = (|a| + |b| - |c|) / (2 * N) := by
  dsimp only
  rw [← norm_eq_sqrt_real_inner n, distance, (segment_plane_isLeast P n hn A B).csInf_eq]
  simp only [segmentValue, div_div, inner_sub_right]
  congr 2
  congr 1
  ring

/-- Both a global lower bound and existence of a closest ray/plane pair. -/
theorem ray_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    IsLeast {r | ∃ x ∈ ray A B, ∃ y ∈ plane P n, dist x y = r}
      (rayValue ⟪n, A - P⟫_ℝ ⟪n, B - A⟫_ℝ / ‖n‖) := by
  rw [ray_eq_image]
  apply plane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, ht, rfl⟩
    rw [ray_residual]
    exact rayValue_le _ _ t ht
  · obtain ⟨t, ht, he⟩ := rayValue_attained ⟪n, A - P⟫_ℝ ⟪n, B - A⟫_ℝ
    exact ⟨_, ⟨t, ht, rfl⟩, by rw [ray_residual, he]⟩

/-- A single sign-based expression valid also for parallel rays. -/
theorem ray_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℝ
    let c := ⟪n, B - A⟫_ℝ
    let N := Real.sqrt ⟪n, n⟫_ℝ
    distance (ray A B) (plane P n) = |a| * (1 + min 0 (Real.sign (a * c))) / N := by
  dsimp only
  rw [← norm_eq_sqrt_real_inner n, distance, (ray_plane_isLeast P n hn A B).csInf_eq,
    rayValue_eq_sign]

/-- Both a global lower bound and existence of a closest line/plane pair. -/
theorem line_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    IsLeast {r | ∃ x ∈ line A B, ∃ y ∈ plane P n, dist x y = r}
      (lineValue ⟪n, A - P⟫_ℝ ⟪n, B - A⟫_ℝ / ‖n‖) := by
  rw [line_eq_range]
  apply plane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, rfl⟩
    rw [line_residual]
    exact lineValue_le _ _ t
  · obtain ⟨t, he⟩ := lineValue_attained ⟪n, A - P⟫_ℝ ⟪n, B - A⟫_ℝ
    exact ⟨_, ⟨t, rfl⟩, by rw [line_residual, he]⟩

/-- Line distance using `sign`, including parallel lines and coincident defining points. -/
theorem line_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℝ
    let c := ⟪n, B - A⟫_ℝ
    let N := Real.sqrt ⟪n, n⟫_ℝ
    distance (line A B) (plane P n) = |a| * (1 - |Real.sign c|) / N := by
  dsimp only
  rw [← norm_eq_sqrt_real_inner n, distance, (line_plane_isLeast P n hn A B).csInf_eq,
    lineValue]

/-- The sign formula is a global lower bound attained by a pair of points on the planes.
For a positive Gram determinant we explicitly construct an intersection point;
when the determinant is zero we project a point of the second plane onto the first. -/
theorem plane_plane_isLeast (P n : E) (hn : n ≠ 0) (Q m : E) (hm : m ≠ 0) :
    let a := ⟪n, Q - P⟫_ℝ
    let Δ := ⟪n, n⟫_ℝ * ⟪m, m⟫_ℝ - ⟪n, m⟫_ℝ ^ 2
    IsLeast {r | ∃ x ∈ plane P n, ∃ y ∈ plane Q m, dist x y = r}
      (|a| * (1 - Real.sign Δ) / ‖n‖) := by
  intro a Δ
  let v := ⟪m, m⟫_ℝ • n - ⟪n, m⟫_ℝ • m
  have hmv : ⟪m, v⟫_ℝ = 0 := by
    dsimp [v]
    simp only [inner_sub_right, real_inner_smul_right, real_inner_comm m n]
    ring
  have hnv : ⟪n, v⟫_ℝ = Δ := by
    dsimp [v, Δ]
    simp only [inner_sub_right, real_inner_smul_right]
    ring
  have hvv : ⟪v, v⟫_ℝ = ⟪m, m⟫_ℝ * Δ := by
    dsimp [v, Δ]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm m n]
    ring
  have hmm : 0 < ⟪m, m⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hm)
  have hΔ : 0 ≤ Δ := by
    have hvnonneg : 0 ≤ ⟪v, v⟫_ℝ := by rw [real_inner_self_eq_norm_sq]; positivity
    rw [hvv] at hvnonneg
    exact nonneg_of_mul_nonneg_right hvnonneg hmm
  by_cases hzero : Δ = 0
  · rw [hzero, Real.sign_zero, sub_zero, mul_one]
    have hvzero : v = 0 := inner_self_eq_zero.mp (by rw [hvv, hzero, mul_zero])
    have hres (y : E) (hy : y ∈ plane Q m) : ⟪n, y - P⟫_ℝ = a := by
      have hmy : ⟪m, y - Q⟫_ℝ = 0 := hy
      have h := congrArg (fun w : E => ⟪w, y - Q⟫_ℝ) hvzero
      simp only [v, inner_sub_left, real_inner_smul_left, hmy, mul_zero,
        sub_zero, inner_zero_left] at h
      have hny : ⟪n, y - Q⟫_ℝ = 0 := (mul_eq_zero.mp h).resolve_left hmm.ne'
      rw [show y - P = (y - Q) + (Q - P) by abel, inner_add_right, hny, zero_add]
    constructor
    · exact ⟨planeProjection P n Q, planeProjection_mem P n hn Q, Q,
        point_mem_plane Q m, by rw [dist_comm, dist_planeProjection P n hn Q]⟩
    · rintro r ⟨x, hx, y, hy, rfl⟩
      simpa only [hres y hy, dist_comm y x] using residual_div_norm_le_dist P n hn y x hx
  · have hpos : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm hzero)
    rw [Real.sign_of_pos hpos, sub_self, mul_zero, zero_div]
    let x := Q - (a / Δ) • v
    have hxP : x ∈ plane P n := by
      change ⟪n, x - P⟫_ℝ = 0
      simp only [x, inner_sub_right, real_inner_smul_right, hnv, div_mul_cancel₀ _ hzero]
      dsimp [a]
      rw [inner_sub_right]
      ring
    have hxQ : x ∈ plane Q m := by
      change ⟪m, x - Q⟫_ℝ = 0
      simp only [x, inner_sub_right, real_inner_smul_right, hmv, mul_zero, sub_zero, sub_self]
    constructor
    · exact ⟨x, hxP, x, hxQ, dist_self x⟩
    · rintro r ⟨y, _, z, _, rfl⟩
      exact dist_nonneg

/-- A single plane-to-plane distance formula using `sign`, including intersecting,
parallel, and coincident planes. Only the two normals must be nonzero. -/
theorem plane_plane_distance (P n : E) (hn : n ≠ 0) (Q m : E) (hm : m ≠ 0) :
    let a := ⟪n, Q - P⟫_ℝ
    let Δ := ⟪n, n⟫_ℝ * ⟪m, m⟫_ℝ - ⟪n, m⟫_ℝ ^ 2
    let N := Real.sqrt ⟪n, n⟫_ℝ
    distance (plane P n) (plane Q m) = |a| * (1 - Real.sign Δ) / N := by
  dsimp only
  rw [← norm_eq_sqrt_real_inner n, distance, (plane_plane_isLeast P n hn Q m hm).csInf_eq]

/-- With the same normal, only the perpendicular displacement between the planes matters. -/
theorem plane_plane_distance_same_normal (P Q n : E) (hn : n ≠ 0) :
    distance (plane P n) (plane Q n) = |⟪n, Q - P⟫_ℝ| / Real.sqrt ⟪n, n⟫_ℝ := by
  rw [plane_plane_distance P n hn Q n hn]
  simp only [pow_two, sub_self, Real.sign_zero, sub_zero, mul_one]

end SympyGeometry
