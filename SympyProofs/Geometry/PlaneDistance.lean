module

public import SympyProofs.Geometry.Basic
public import SympyProofs.Geometry.ScalarDistance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Euclidean distances from planes to segments, rays, and lines

For `plane P n`, `segment A B`, `ray A B`, and `line A B`, write
`a = ⟪n, A - P⟫`, `b = ⟪n, B - P⟫`, and `c = ⟪n, B - A⟫`.
The segment distance is
`(|a| + |b| - |b - a|) / (2 * ‖n‖)`.
The ray distance is `|a| * (1 + min 0 (Real.sign (a * c))) / ‖n‖`.
The line distance is `|a| * (1 - |Real.sign c|) / ‖n‖`.

Planes, segments, rays, and lines use the set-based definitions in `SympyGeometry`.
The only nondegeneracy assumption is `n ≠ 0`, needed for a proper plane.
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
    distance (segment A B) (plane P n) =
      (|⟪n, A - P⟫_ℝ| + |⟪n, B - P⟫_ℝ| - |⟪n, B - A⟫_ℝ|) /
        (2 * ‖n‖) := by
  rw [distance, (segment_plane_isLeast P n hn A B).csInf_eq]
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
    distance (ray A B) (plane P n) =
      |⟪n, A - P⟫_ℝ| * (1 + min 0 (Real.sign (⟪n, A - P⟫_ℝ * ⟪n, B - A⟫_ℝ))) /
        ‖n‖ := by
  rw [distance, (ray_plane_isLeast P n hn A B).csInf_eq, rayValue_eq_sign]

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
    distance (line A B) (plane P n) =
      |⟪n, A - P⟫_ℝ| * (1 - |Real.sign ⟪n, B - A⟫_ℝ|) / ‖n‖ := by
  rw [distance, (line_plane_isLeast P n hn A B).csInf_eq, lineValue]

end SympyGeometry
