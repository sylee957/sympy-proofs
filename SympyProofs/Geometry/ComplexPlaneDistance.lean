module

public import SympyProofs.Geometry.PlaneDistance
public import SympyProofs.Geometry.ComplexScalarDistance

/-!
# Distances to complex hyperplanes

`complexPlane P n` is the zero set of the Hermitian residual `⟪n, x - P⟫_ℂ`.
Segments, rays, and lines retain their real parameters; a line here is a real
affine line in a complex inner product space, not a complex affine line.

Write `a = ⟪n, A - P⟫`, `c = ⟪n, B - A⟫`, `β = re (conj a * c)`,
`γ = ‖c‖ ^ 2`, and `u = -β / (γ + 1 - sign γ)`. The distance is
`‖a + t * c‖ / sqrt (re ⟪n, n⟫)`, with `t = min 1 (max 0 u)` for a segment,
`t = max 0 u` for a ray, and `t = u` for a line. The denominator defining
`u` is strictly positive, even when `c = 0`.

The only nondegeneracy hypothesis is `n ≠ 0`. In particular, all formulas
include zero slopes and coincident defining points. We prove that these are
the infima of actual pairwise distances and that a closest pair exists.
-/

@[expose] public section

namespace SympyGeometry

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- The complex hyperplane through `P` with Hermitian normal `n`. -/
def complexPlane (P n : E) : Set E := {x | ⟪n, x - P⟫_ℂ = 0}

@[simp] theorem mem_complexPlane (P n x : E) :
    x ∈ complexPlane P n ↔ ⟪n, x - P⟫_ℂ = 0 := Iff.rfl

theorem mem_complexPlane_iff_inner_eq (P n x : E) :
    x ∈ complexPlane P n ↔ ⟪n, x⟫_ℂ = ⟪n, P⟫_ℂ := by
  simp [inner_sub_right, sub_eq_zero]

@[simp] theorem point_mem_complexPlane (P n : E) : P ∈ complexPlane P n := by
  simp

/-- Complex Cauchy--Schwarz bounds the distance to every point of the hyperplane. -/
theorem complex_residual_div_norm_le_dist (P n : E) (hn : n ≠ 0)
    (x y : E) (hy : y ∈ complexPlane P n) :
    ‖⟪n, x - P⟫_ℂ‖ / ‖n‖ ≤ dist x y := by
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  have h := norm_inner_le_norm (𝕜 := ℂ) n (x - y)
  rw [inner_sub_right, (mem_complexPlane_iff_inner_eq P n y).mp hy] at h
  simpa only [inner_sub_right, dist_eq_norm, mul_comm] using h

/-- Orthogonal projection onto a complex hyperplane. -/
noncomputable def complexPlaneProjection (P n x : E) : E :=
  x - (⟪n, x - P⟫_ℂ / (‖n‖ : ℂ) ^ 2) • n

theorem complexPlaneProjection_mem (P n : E) (hn : n ≠ 0) (x : E) :
    complexPlaneProjection P n x ∈ complexPlane P n := by
  have hnorm : (‖n‖ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hself : ⟪n, n⟫_ℂ = (‖n‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K n
  rw [mem_complexPlane_iff_inner_eq]
  change ⟪n, x - (⟪n, x - P⟫_ℂ / (‖n‖ : ℂ) ^ 2) • n⟫_ℂ = ⟪n, P⟫_ℂ
  rw [inner_sub_right, inner_smul_right, hself,
    div_mul_cancel₀ _ hnorm, inner_sub_right]
  ring

theorem dist_complexPlaneProjection (P n : E) (hn : n ≠ 0) (x : E) :
    dist x (complexPlaneProjection P n x) = ‖⟪n, x - P⟫_ℂ‖ / ‖n‖ := by
  have hnorm : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  rw [dist_eq_norm, complexPlaneProjection, sub_sub_cancel, norm_smul,
    norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg n)]
  field_simp

/-- Point-to-complex-hyperplane distance. -/
theorem infDist_complexPlane (P n : E) (hn : n ≠ 0) (x : E) :
    Metric.infDist x (complexPlane P n) = ‖⟪n, x - P⟫_ℂ‖ / ‖n‖ := by
  have hp := complexPlaneProjection_mem P n hn x
  apply le_antisymm
  · calc
      _ ≤ dist x (complexPlaneProjection P n x) := Metric.infDist_le_dist_of_mem hp
      _ = _ := dist_complexPlaneProjection P n hn x
  · exact (Metric.le_infDist ⟨_, hp⟩).mpr fun y hy =>
      complex_residual_div_norm_le_dist P n hn x y hy

/-- Lift an attained minimum of the complex residual norm to a closest geometric pair. -/
theorem complexPlane_distance_isLeast_of_residual (P n : E) (hn : n ≠ 0)
    (S : Set E) (m : ℝ)
    (hlower : ∀ x ∈ S, m ≤ ‖⟪n, x - P⟫_ℂ‖)
    (hattain : ∃ x ∈ S, ‖⟪n, x - P⟫_ℂ‖ = m) :
    IsLeast {r | ∃ x ∈ S, ∃ y ∈ complexPlane P n, dist x y = r} (m / ‖n‖) := by
  constructor
  · obtain ⟨x, hx, he⟩ := hattain
    exact ⟨x, hx, complexPlaneProjection P n x, complexPlaneProjection_mem P n hn x,
      by rw [dist_complexPlaneProjection P n hn x, he]⟩
  · rintro r ⟨x, hx, y, hy, rfl⟩
    calc
      m / ‖n‖ ≤ ‖⟪n, x - P⟫_ℂ‖ / ‖n‖ :=
        div_le_div_of_nonneg_right (hlower x hx) (norm_nonneg n)
      _ ≤ dist x y := complex_residual_div_norm_le_dist P n hn x y hy

theorem complex_affine_residual (P n A B : E) (t : ℝ) :
    ⟪n, A + t • (B - A) - P⟫_ℂ =
      ⟪n, A - P⟫_ℂ + (t : ℂ) * ⟪n, B - A⟫_ℂ := by
  change ⟪n, A + (t : ℂ) • (B - A) - P⟫_ℂ = _
  simp only [inner_sub_right, inner_add_right, inner_smul_right]
  ring

theorem complex_segment_residual (P n A B : E) (t : ℝ) :
    ⟪n, (1 - t) • A + t • B - P⟫_ℂ =
      ⟪n, A - P⟫_ℂ + (t : ℂ) * ⟪n, B - A⟫_ℂ := by
  have he : (1 - t) • A + t • B = A + t • (B - A) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [he, complex_affine_residual]

/-- The segment minimum is attained by clamping the real quadratic minimizer. -/
theorem segment_complex_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    IsLeast {r | ∃ x ∈ segment A B, ∃ y ∈ complexPlane P n, dist x y = r}
      (‖a + (complexSegmentParam a c : ℂ) * c‖ / ‖n‖) := by
  dsimp only
  rw [segment_eq_image]
  apply complexPlane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, ht, rfl⟩
    rw [complex_segment_residual]
    exact complexSegmentParam_le _ _ t ht
  · refine ⟨_, ⟨complexSegmentParam ⟪n, A - P⟫_ℂ ⟪n, B - A⟫_ℂ,
      complexSegmentParam_mem _ _, rfl⟩, ?_⟩
    rw [complex_segment_residual]

/-- The ray minimum is attained by clamping the real quadratic minimizer below at zero. -/
theorem ray_complex_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    IsLeast {r | ∃ x ∈ ray A B, ∃ y ∈ complexPlane P n, dist x y = r}
      (‖a + (complexRayParam a c : ℂ) * c‖ / ‖n‖) := by
  dsimp only
  rw [ray_eq_image]
  apply complexPlane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, ht, rfl⟩
    rw [complex_affine_residual]
    exact complexRayParam_le _ _ t ht
  · refine ⟨_, ⟨complexRayParam ⟪n, A - P⟫_ℂ ⟪n, B - A⟫_ℂ,
      complexRayParam_nonneg _ _, rfl⟩, ?_⟩
    rw [complex_affine_residual]

/-- The real affine line minimum is attained by the unconstrained quadratic minimizer. -/
theorem line_complex_plane_isLeast (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    IsLeast {r | ∃ x ∈ line A B, ∃ y ∈ complexPlane P n, dist x y = r}
      (‖a + (complexLineParam a c : ℂ) * c‖ / ‖n‖) := by
  dsimp only
  rw [line_eq_range]
  apply complexPlane_distance_isLeast_of_residual P n hn
  · rintro x ⟨t, rfl⟩
    rw [complex_affine_residual]
    exact complexLineParam_le _ _ t
  · refine ⟨_, ⟨complexLineParam ⟪n, A - P⟫_ℂ ⟪n, B - A⟫_ℂ, rfl⟩, ?_⟩
    rw [complex_affine_residual]

/-- Segment distance to a complex hyperplane, including zero normal slope. -/
theorem segment_complex_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    let β := (star a * c).re
    let γ := ‖c‖ ^ 2
    let u := -β / (γ + 1 - Real.sign γ)
    let t := min 1 (max 0 u)
    let N := Real.sqrt (⟪n, n⟫_ℂ).re
    distance (segment A B) (complexPlane P n) = ‖a + (t : ℂ) * c‖ / N := by
  dsimp only
  have hN : Real.sqrt (⟪n, n⟫_ℂ).re = ‖n‖ :=
    (norm_eq_sqrt_re_inner (𝕜 := ℂ) n).symm
  rw [hN]
  exact (segment_complex_plane_isLeast P n hn A B).csInf_eq

/-- Ray distance to a complex hyperplane, including zero normal slope. -/
theorem ray_complex_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    let β := (star a * c).re
    let γ := ‖c‖ ^ 2
    let u := -β / (γ + 1 - Real.sign γ)
    let t := max 0 u
    let N := Real.sqrt (⟪n, n⟫_ℂ).re
    distance (ray A B) (complexPlane P n) = ‖a + (t : ℂ) * c‖ / N := by
  dsimp only
  have hN : Real.sqrt (⟪n, n⟫_ℂ).re = ‖n‖ :=
    (norm_eq_sqrt_re_inner (𝕜 := ℂ) n).symm
  rw [hN]
  exact (ray_complex_plane_isLeast P n hn A B).csInf_eq

/-- Real affine line distance to a complex hyperplane, including zero normal slope. -/
theorem line_complex_plane_distance (P n : E) (hn : n ≠ 0) (A B : E) :
    let a := ⟪n, A - P⟫_ℂ
    let c := ⟪n, B - A⟫_ℂ
    let β := (star a * c).re
    let γ := ‖c‖ ^ 2
    let u := -β / (γ + 1 - Real.sign γ)
    let N := Real.sqrt (⟪n, n⟫_ℂ).re
    distance (line A B) (complexPlane P n) = ‖a + (u : ℂ) * c‖ / N := by
  dsimp only
  have hN : Real.sqrt (⟪n, n⟫_ℂ).re = ‖n‖ :=
    (norm_eq_sqrt_re_inner (𝕜 := ℂ) n).symm
  rw [hN]
  exact (line_complex_plane_isLeast P n hn A B).csInf_eq

end SympyGeometry
