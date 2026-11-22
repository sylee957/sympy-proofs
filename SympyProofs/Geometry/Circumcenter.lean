module

public import SympyProofs.Geometry.PointConicDistance

/-!
# Circles through three points

`IsEquidistant Y P₁ P₂ P₃` says that `Y` is at the same distance from the three
points. `IsCircumcenter Y P₁ P₂ P₃` adds that the three points are distinct, so
that `Y` is the centre of a circle through them. `circumcenters T` is the set of
such centres for triples of points of a set `T`.

Three distinct points on a line have no equidistant point, so they contribute
nothing to `circumcenters T`. `exists_equidistant` gives the centre for three
points that are not on a line.

`SympyProofs.Geometry.Evolute` uses these to define the centre of curvature as
a limit of circle centres.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

/-- Equal distances from `Y`, in coordinates. -/
theorem dist_eq_iff_coordinates (Y P Q : Point2D) :
    dist Y P = dist Y Q ↔
      (Y 0 - P 0) ^ 2 + (Y 1 - P 1) ^ 2 = (Y 0 - Q 0) ^ 2 + (Y 1 - Q 1) ^ 2 := by
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_sq_pointDistanceSq, dist_sq_pointDistanceSq]
  rfl

/-- `Y` is at the same distance from `P₁`, `P₂` and `P₃`. -/
def IsEquidistant (Y P₁ P₂ P₃ : Point2D) : Prop :=
  dist Y P₁ = dist Y P₂ ∧ dist Y P₂ = dist Y P₃

/-- `Y` is the centre of a circle through the three distinct points `P₁`, `P₂`, `P₃`. -/
def IsCircumcenter (Y P₁ P₂ P₃ : Point2D) : Prop :=
  P₁ ≠ P₂ ∧ P₂ ≠ P₃ ∧ P₁ ≠ P₃ ∧ IsEquidistant Y P₁ P₂ P₃

/-- The centres of the circles through three distinct points of `T`. Three points on a
line have no such centre. -/
def circumcenters (T : Set Point2D) : Set Point2D :=
  {Y | ∃ P₁ ∈ T, ∃ P₂ ∈ T, ∃ P₃ ∈ T, IsCircumcenter Y P₁ P₂ P₃}

theorem circumcenters_mono {T T' : Set Point2D} (h : T ⊆ T') :
    circumcenters T ⊆ circumcenters T' := by
  rintro Y ⟨P₁, h₁, P₂, h₂, P₃, h₃, hY⟩
  exact ⟨P₁, h h₁, P₂, h h₂, P₃, h h₃, hY⟩

/-- Three points not on a line have an equidistant point. -/
theorem exists_equidistant (A B C : Point2D)
    (h : (B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0) ≠ 0) :
    ∃ Y : Point2D, IsEquidistant Y A B C := by
  have h2 : 2 * ((B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0)) ≠ 0 :=
    mul_ne_zero two_ne_zero h
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ,
      y₀ * (2 * ((B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0))) =
        (B 0 ^ 2 + B 1 ^ 2 - A 0 ^ 2 - A 1 ^ 2) * (C 1 - B 1) -
          (C 0 ^ 2 + C 1 ^ 2 - B 0 ^ 2 - B 1 ^ 2) * (B 1 - A 1) :=
    ⟨_, div_mul_cancel₀ _ h2⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ℝ,
      y₁ * (2 * ((B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0))) =
        (B 0 - A 0) * (C 0 ^ 2 + C 1 ^ 2 - B 0 ^ 2 - B 1 ^ 2) -
          (C 0 - B 0) * (B 0 ^ 2 + B 1 ^ 2 - A 0 ^ 2 - A 1 ^ 2) :=
    ⟨_, div_mul_cancel₀ _ h2⟩
  refine ⟨!₂[y₀, y₁], ?_, ?_⟩
  · rw [dist_eq_iff_coordinates]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    apply mul_left_cancel₀ h2
    linear_combination 2 * (B 0 - A 0) * hy₀ + 2 * (B 1 - A 1) * hy₁
  · rw [dist_eq_iff_coordinates]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    apply mul_left_cancel₀ h2
    linear_combination 2 * (C 0 - B 0) * hy₀ + 2 * (C 1 - B 1) * hy₁

end

end SympyGeometry
