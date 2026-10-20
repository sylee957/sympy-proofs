module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Set-based segments, rays, lines, and planes

All four objects are sets in a real inner product space, with names scoped
to `SympyGeometry`. The arguments match SymPy's constructors: `plane P n`
uses a point on the plane and a normal vector, `segment A B` uses two endpoints,
`ray A B` starts at `A` and passes through `B`, and `line A B` passes through
both points with an unrestricted real parameter.

The ray and line direction is `B - A`. We also allow `A = B`, giving the singleton
`{A}` for segments, rays, and lines. A plane is a proper hyperplane when its
normal is nonzero; a zero normal gives the whole space.
-/

@[expose] public section

namespace SympyGeometry

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The plane through `P` with normal vector `n` (a hyperplane in general dimension). -/
def plane (P n : E) : Set E := {x | ⟪n, x - P⟫_ℝ = 0}

/-- The dot-product equation characterizes membership in the plane. -/
@[simp] theorem mem_plane (P n x : E) :
    x ∈ plane P n ↔ ⟪n, x - P⟫_ℝ = 0 := Iff.rfl

/-- The equivalent equation with the offset determined by the defining point. -/
theorem mem_plane_iff_inner_eq (P n x : E) :
    x ∈ plane P n ↔ ⟪n, x⟫_ℝ = ⟪n, P⟫_ℝ := by
  simp [inner_sub_right, sub_eq_zero]

/-- The usual plane equation as a set equality. -/
theorem plane_eq_setOf (P n : E) :
    plane P n = {x | ⟪n, x - P⟫_ℝ = 0} := rfl

@[simp] theorem point_mem_plane (P n : E) : P ∈ plane P n := by
  simp

/-- The closed segment with endpoints `A` and `B`, allowing `A = B`. -/
def segment (A B : E) : Set E :=
  (fun t : ℝ => (1 - t) • A + t • B) '' Set.Icc 0 1

/-- The parameterization of the closed segment. -/
theorem segment_eq_image (A B : E) :
    segment A B = (fun t : ℝ => (1 - t) • A + t • B) '' Set.Icc 0 1 := rfl

theorem mem_segment_iff (A B x : E) :
    x ∈ segment A B ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • A + t • B = x := Iff.rfl

/-- A segment with equal endpoints is a singleton. -/
@[simp] theorem segment_self (A : E) : segment A A = {A} := by
  simp [segment, ← add_smul]

/-- The closed ray starting at `A` and passing through `B`, allowing `A = B`. -/
def ray (A B : E) : Set E := (fun t : ℝ => A + t • (B - A)) '' Set.Ici 0

/-- The parameterization of the closed ray. -/
theorem ray_eq_image (A B : E) :
    ray A B = (fun t : ℝ => A + t • (B - A)) '' Set.Ici 0 := rfl

theorem mem_ray_iff (A B x : E) :
    x ∈ ray A B ↔ ∃ t : ℝ, 0 ≤ t ∧ A + t • (B - A) = x := Iff.rfl

/-- Equal defining points give the source alone. -/
@[simp] theorem ray_self (A : E) : ray A A = {A} := by
  simp [ray]

/-- Moving the second point a positive multiple of its displacement from the source
leaves the ray unchanged, including when the defining points coincide. -/
theorem ray_pos_smul (A B : E) (c : ℝ) (hc : 0 < c) :
    ray A (A + c • (B - A)) = ray A B := by
  ext x
  rw [mem_ray_iff, mem_ray_iff]
  simp only [add_sub_cancel_left]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * c, mul_nonneg ht hc.le, by rw [mul_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t / c, div_nonneg ht hc.le, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩

/-- The line through `A` and `B`, allowing `A = B` as a singleton. -/
def line (A B : E) : Set E := Set.range (fun t : ℝ => A + t • (B - A))

/-- The parameterization of the line over all real numbers. -/
theorem line_eq_range (A B : E) :
    line A B = Set.range (fun t : ℝ => A + t • (B - A)) := rfl

theorem mem_line_iff (A B x : E) :
    x ∈ line A B ↔ ∃ t : ℝ, A + t • (B - A) = x := Iff.rfl

/-- Equal defining points give a singleton. -/
@[simp] theorem line_self (A : E) : line A A = {A} := by
  simp [line]

end SympyGeometry
