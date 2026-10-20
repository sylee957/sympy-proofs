module

public import SympyProofs.Geometry.PlaneDistance

/-!
# Explicit coordinate formulas in Euclidean three-space

`Point3D` has the Euclidean metric. Its coordinates `X 0`, `X 1`, `X 2`
are x, y, z; a point or normal vector can be written as `!₂[x, y, z]`.
The constructors remain `plane P n`, `segment A B`, `ray A B`, and `line A B`.

The distance formulas below expand every inner product and norm into real
coordinate arithmetic. The only nondegeneracy assumption is `n ≠ 0`.
The ray and line formulas use `Real.sign`, including when the direction is parallel
to the plane or the two defining points coincide.
-/

@[expose] public section

namespace SympyGeometry

open scoped InnerProductSpace

/-- Real three-space with its Euclidean metric, also used for normal vectors. -/
abbrev Point3D := EuclideanSpace ℝ (Fin 3)

/-- The dot product of a normal with a displacement, in x, y, z coordinates. -/
theorem inner_sub_eq_coordinates_3d (n X P : Point3D) :
    ⟪n, X - P⟫_ℝ =
      n 0 * (X 0 - P 0) + n 1 * (X 1 - P 1) + n 2 * (X 2 - P 2) := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, add_assoc, mul_comm]

/-- Euclidean length in three coordinates. -/
theorem norm_eq_coordinates_3d (n : Point3D) :
    ‖n‖ = Real.sqrt (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.norm_eq_abs, add_assoc]

/-- The equation of the plane through `P` with normal `n`, fully expanded. -/
theorem mem_plane_3d (P n X : Point3D) :
    X ∈ plane P n ↔
      n 0 * (X 0 - P 0) + n 1 * (X 1 - P 1) + n 2 * (X 2 - P 2) = 0 := by
  rw [mem_plane, inner_sub_eq_coordinates_3d]

/-- Point-to-plane distance in explicit coordinates. -/
theorem infDist_plane_3d (P n : Point3D) (hn : n ≠ 0) (X : Point3D) :
    Metric.infDist X (plane P n) =
      |n 0 * (X 0 - P 0) + n 1 * (X 1 - P 1) + n 2 * (X 2 - P 2)| /
        Real.sqrt (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
  rw [infDist_plane P n hn X, inner_sub_eq_coordinates_3d, norm_eq_coordinates_3d]

/-- Segment-to-plane distance using only real coordinate arithmetic and absolute values.
It includes parallel segments, intersections, and coincident endpoints. -/
theorem segment_plane_distance_3d (P n : Point3D) (hn : n ≠ 0) (A B : Point3D) :
    distance (segment A B) (plane P n) =
      (|n 0 * (A 0 - P 0) + n 1 * (A 1 - P 1) + n 2 * (A 2 - P 2)| +
        |n 0 * (B 0 - P 0) + n 1 * (B 1 - P 1) + n 2 * (B 2 - P 2)| -
        |n 0 * (B 0 - A 0) + n 1 * (B 1 - A 1) + n 2 * (B 2 - A 2)|) /
        (2 * Real.sqrt (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2)) := by
  rw [segment_plane_distance P n hn A B, ← norm_eq_sqrt_real_inner n]
  simp only [inner_sub_eq_coordinates_3d, norm_eq_coordinates_3d]

/-- Ray-to-plane distance using explicit coordinates and `sign`, without an `if` branch
or division by the normal component of the direction. -/
theorem ray_plane_distance_3d (P n : Point3D) (hn : n ≠ 0) (A B : Point3D) :
    distance (ray A B) (plane P n) =
      |n 0 * (A 0 - P 0) + n 1 * (A 1 - P 1) + n 2 * (A 2 - P 2)| *
        (1 + min 0 (Real.sign
          ((n 0 * (A 0 - P 0) + n 1 * (A 1 - P 1) + n 2 * (A 2 - P 2)) *
            (n 0 * (B 0 - A 0) + n 1 * (B 1 - A 1) + n 2 * (B 2 - A 2))))) /
        Real.sqrt (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
  rw [ray_plane_distance P n hn A B, ← norm_eq_sqrt_real_inner n]
  simp only [inner_sub_eq_coordinates_3d, norm_eq_coordinates_3d]

/-- Line-to-plane distance using explicit coordinates and `sign`, without an `if` branch
or division by the normal component of the direction. -/
theorem line_plane_distance_3d (P n : Point3D) (hn : n ≠ 0) (A B : Point3D) :
    distance (line A B) (plane P n) =
      |n 0 * (A 0 - P 0) + n 1 * (A 1 - P 1) + n 2 * (A 2 - P 2)| *
        (1 - |Real.sign
          (n 0 * (B 0 - A 0) + n 1 * (B 1 - A 1) + n 2 * (B 2 - A 2))|) /
        Real.sqrt (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) := by
  rw [line_plane_distance P n hn A B, ← norm_eq_sqrt_real_inner n]
  simp only [inner_sub_eq_coordinates_3d, norm_eq_coordinates_3d]

end SympyGeometry
