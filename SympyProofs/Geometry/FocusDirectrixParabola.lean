module

public import SympyProofs.Geometry.PointConicDistance

/-!
# Distance to a parabola given by its focus and directrix

`focusDirectrixParabola F directrix` is the locus of points equidistant from
the focus `F` and the directrix, matching the geometric meaning of SymPy's
constructor. The distance formula takes `line A B` as its directrix and allows
any orientation. Its hypotheses require distinct defining points and a focus
off the directrix.

An explicit Euclidean change of coordinates turns the directrix into the
horizontal axis and the parabola into the vertex form used in
`PointConicDistance`. The final formula uses local `let` bindings for the
coordinate change and Cardano radicals.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open scoped InnerProductSpace

/-- The focus/directrix definition: equal distances to a point and a set. -/
def focusDirectrixParabola (F : Point2D) (directrix : Set Point2D) : Set Point2D :=
  {Y | dist Y F = Metric.infDist Y directrix}

@[simp] theorem mem_focusDirectrixParabola (F Y : Point2D) (directrix : Set Point2D) :
    Y ∈ focusDirectrixParabola F directrix ↔ dist Y F = Metric.infDist Y directrix := Iff.rfl

/-- The focus/directrix construction commutes with Euclidean isometries. -/
theorem focusDirectrixParabola_image (e : Point2D ≃ᵢ Point2D)
    (F : Point2D) (directrix : Set Point2D) :
    e '' focusDirectrixParabola F directrix = focusDirectrixParabola (e F) (e '' directrix) := by
  ext Y
  obtain ⟨Y, rfl⟩ := e.surjective Y
  simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right,
    mem_focusDirectrixParabola, e.dist_eq, Metric.infDist_image e.isometry]

/-- Coordinates along the unit direction `(u, v)` and its counterclockwise normal. -/
def orthonormalCoordinates (A : Point2D) (u v : ℝ) (hunit : u ^ 2 + v ^ 2 = 1) :
    Point2D ≃ᵢ Point2D where
  toFun X := !₂[u * (X 0 - A 0) + v * (X 1 - A 1),
    -v * (X 0 - A 0) + u * (X 1 - A 1)]
  invFun Y := A + !₂[u * Y 0 - v * Y 1, v * Y 0 + u * Y 1]
  left_inv X := by
    ext i
    fin_cases i <;> dsimp
    · linear_combination (X 0 - A 0) * hunit
    · linear_combination (X 1 - A 1) * hunit
  right_inv Y := by
    ext i
    fin_cases i <;> dsimp
    · linear_combination Y 0 * hunit
    · linear_combination Y 1 * hunit
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro X Y
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_sq_pointDistanceSq, pointDistanceSq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2) * hunit

@[simp] theorem orthonormalCoordinates_apply (A X : Point2D) (u v : ℝ)
    (hunit : u ^ 2 + v ^ 2 = 1) :
    orthonormalCoordinates A u v hunit X =
      !₂[u * (X 0 - A 0) + v * (X 1 - A 1),
        -v * (X 0 - A 0) + u * (X 1 - A 1)] := rfl

private theorem infDist_horizontal_axis (Y : Point2D) :
    Metric.infDist Y {Z : Point2D | Z 1 = 0} = |Y 1| := by
  have hn : (!₂[0, 1] : Point2D) ≠ 0 := by
    intro h
    have := congrArg (fun X : Point2D => X 1) h
    norm_num at this
  have he : {Z : Point2D | Z 1 = 0} = plane (0 : Point2D) !₂[0, 1] := by
    ext Z
    simp [plane, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  rw [he, infDist_plane _ _ hn]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    EuclideanSpace.norm_eq]

/-- A focus at `(f, g)` and directrix `y = 0` give vertex `(f, g / 2)`
and quadratic coefficient `1 / (2 * g)`. -/
theorem focusDirectrixParabola_horizontal (f g : ℝ) (hg : g ≠ 0) :
    focusDirectrixParabola !₂[f, g] {Z : Point2D | Z 1 = 0} =
      parabola !₂[f, g / 2] (1 / (2 * g)) := by
  ext Y
  rw [mem_focusDirectrixParabola, infDist_horizontal_axis]
  rw [← sq_eq_sq₀ dist_nonneg (abs_nonneg (Y 1))]
  simp only [dist_sq_pointDistanceSq, pointDistanceSq, sq_abs, parabola, Set.mem_ofPred_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · intro h
    field_simp
    nlinarith [h]
  · intro h
    field_simp at h
    nlinarith [h]

/-- Length of the direction used to specify the directrix. -/
def directrixLength (A B : Point2D) : ℝ := Real.sqrt (pointDistanceSq B A)

theorem directrixLength_pos (A B : Point2D) (hAB : A ≠ B) : 0 < directrixLength A B := by
  rw [directrixLength, ← point_distance_coordinates]
  exact dist_pos.mpr hAB.symm

theorem directrixLength_sq (A B : Point2D) :
    directrixLength A B ^ 2 = (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by
  rw [directrixLength, ← point_distance_coordinates, dist_sq_pointDistanceSq]
  rfl

/-- Move `A` to the origin and the directrix direction to the positive horizontal axis. -/
def directrixCoordinates (A B : Point2D) (hAB : A ≠ B) : Point2D ≃ᵢ Point2D :=
  orthonormalCoordinates A ((B 0 - A 0) / directrixLength A B)
    ((B 1 - A 1) / directrixLength A B) (by
      rw [div_pow, div_pow, ← add_div, ← directrixLength_sq]
      exact div_self (pow_ne_zero 2 (directrixLength_pos A B hAB).ne'))

private theorem directrixCoordinates_line_point (A B : Point2D) (hAB : A ≠ B) (t : ℝ) :
    directrixCoordinates A B hAB (A + t • (B - A)) = !₂[t * directrixLength A B, 0] := by
  have hn := (directrixLength_pos A B hAB).ne'
  have hs := directrixLength_sq A B
  ext i
  fin_cases i
  · change (B 0 - A 0) / directrixLength A B * (A 0 + t * (B 0 - A 0) - A 0) +
      (B 1 - A 1) / directrixLength A B * (A 1 + t * (B 1 - A 1) - A 1) =
        t * directrixLength A B
    field_simp
    linear_combination -t * hs
  · change -((B 1 - A 1) / directrixLength A B) * (A 0 + t * (B 0 - A 0) - A 0) +
      (B 0 - A 0) / directrixLength A B * (A 1 + t * (B 1 - A 1) - A 1) = 0
    ring

theorem directrixCoordinates_line (A B : Point2D) (hAB : A ≠ B) :
    directrixCoordinates A B hAB '' line A B = {Y : Point2D | Y 1 = 0} := by
  rw [line, ← Set.range_comp]
  simp only [Function.comp_def]
  simp_rw [directrixCoordinates_line_point]
  ext Y
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hY
    refine ⟨Y 0 / directrixLength A B, ?_⟩
    ext i
    fin_cases i
    · exact div_mul_cancel₀ _ (directrixLength_pos A B hAB).ne'
    · exact hY.symm

theorem directrixCoordinates_focus_ne_zero (F A B : Point2D)
    (hAB : A ≠ B) (hF : F ∉ line A B) : (directrixCoordinates A B hAB F) 1 ≠ 0 := by
  intro h
  have hm : directrixCoordinates A B hAB F ∈ directrixCoordinates A B hAB '' line A B := by
    rw [directrixCoordinates_line]
    exact h
  obtain ⟨Y, hY, he⟩ := hm
  exact hF ((directrixCoordinates A B hAB).injective he ▸ hY)

/-- The focus/directrix parabola is an isometric image of a vertex-form parabola. -/
theorem focusDirectrixParabola_eq_vertex_image (F A B : Point2D)
    (hAB : A ≠ B) (hF : F ∉ line A B) :
    let e := directrixCoordinates A B hAB
    let f := (e F) 0
    let g := (e F) 1
    focusDirectrixParabola F (line A B) = e.symm '' parabola !₂[f, g / 2] (1 / (2 * g)) := by
  intro e f g
  have hg : g ≠ 0 := directrixCoordinates_focus_ne_zero F A B hAB hF
  have heF : e F = !₂[f, g] := by ext i; fin_cases i <;> rfl
  have he : e '' focusDirectrixParabola F (line A B) =
      parabola !₂[f, g / 2] (1 / (2 * g)) := by
    rw [focusDirectrixParabola_image, directrixCoordinates_line, heF,
      focusDirectrixParabola_horizontal f g hg]
  have h := congrArg (fun S : Set Point2D => e.symm '' S) he
  simpa only [Set.image_image, Function.comp_def, e.symm_apply_apply, Set.image_id'] using h

/-- Distance computed from the focus and two points specifying the directrix. -/
def pointFocusDirectrixParabolaDistance (X F A B : Point2D) : ℝ :=
  let L := directrixLength A B
  let e₁ := (B 0 - A 0) / L
  let e₂ := (B 1 - A 1) / L
  let f := e₁ * (F 0 - A 0) + e₂ * (F 1 - A 1)
  let g := -e₂ * (F 0 - A 0) + e₁ * (F 1 - A 1)
  let Y := !₂[e₁ * (X 0 - A 0) + e₂ * (X 1 - A 1),
    -e₂ * (X 0 - A 0) + e₁ * (X 1 - A 1)]
  pointParabolaDistance Y !₂[f, g / 2] (1 / (2 * g))

theorem point_focus_directrix_parabola_distance_eq (X F A B : Point2D)
    (hAB : A ≠ B) (hF : F ∉ line A B) :
    Metric.infDist X (focusDirectrixParabola F (line A B)) =
      pointFocusDirectrixParabolaDistance X F A B := by
  let e := directrixCoordinates A B hAB
  let f := (e F) 0
  let g := (e F) 1
  have hg : g ≠ 0 := directrixCoordinates_focus_ne_zero F A B hAB hF
  have ha : 1 / (2 * g) ≠ 0 := one_div_ne_zero (mul_ne_zero (by norm_num) hg)
  change Metric.infDist X (focusDirectrixParabola F (line A B)) =
    pointParabolaDistance (e X) !₂[f, g / 2] (1 / (2 * g))
  rw [focusDirectrixParabola_eq_vertex_image F A B hAB hF]
  simpa only [IsometryEquiv.symm_symm] using
    point_parabola_distance_isometric e.symm X !₂[f, g / 2] (1 / (2 * g)) ha

/-- A closed radical formula for a focus/directrix parabola in any orientation.
`g` is the signed focus-to-directrix distance; `(u, v)` are the query point's
coordinates relative to the vertex, with the directrix horizontal in this frame.
The only assumptions are a genuine directrix line and a focus off that line. -/
theorem point_focus_directrix_parabola_distance (X F A B : Point2D)
    (hAB : A ≠ B) (hF : F ∉ line A B) :
    let dx := B 0 - A 0
    let dy := B 1 - A 1
    let L := Real.sqrt (dx ^ 2 + dy ^ 2)
    let e₁ := dx / L
    let e₂ := dy / L
    let f := e₁ * (F 0 - A 0) + e₂ * (F 1 - A 1)
    let g := -e₂ * (F 0 - A 0) + e₁ * (F 1 - A 1)
    let u := e₁ * (X 0 - A 0) + e₂ * (X 1 - A 1) - f
    let v := -e₂ * (X 0 - A 0) + e₁ * (X 1 - A 1) - g / 2
    let inv := fun z : ℂ => (Real.sign ‖z‖ : ℂ) / (z + ((1 - Real.sign ‖z‖ : ℝ) : ℂ))
    let p : ℂ := (2 * g * (g - v) : ℝ)
    let q : ℂ := (-2 * g ^ 2 * u : ℝ)
    let d := sqrtC (q ^ 2 / 4 + p ^ 3 / 27)
    let c₁ := cbrtC (-q / 2 + d)
    let c₂ := cbrtC (-q / 2 - d)
    let c := c₁ + ((1 - Real.sign ‖c₁‖ : ℝ) : ℂ) * c₂
    let z := c - p / 3 * inv c
    let s := sqrtC (-3 * z ^ 2 - 4 * p)
    let D := fun t : ℝ => (t - u) ^ 2 + (t ^ 2 / (2 * g) - v) ^ 2
    Metric.infDist X (focusDirectrixParabola F (line A B)) = Real.sqrt
      (min (D z.re) (min (D ((-z + s) / 2).re)
        (min (D ((-z - s) / 2).re) (u ^ 2 + v ^ 2)))) := by
  intro dx dy L e₁ e₂ f g u v inv p q d c₁ c₂ c z s D
  let e := directrixCoordinates A B hAB
  have hg : g ≠ 0 := directrixCoordinates_focus_ne_zero F A B hAB hF
  have ha : 1 / (2 * g) ≠ 0 := one_div_ne_zero (mul_ne_zero (by norm_num) hg)
  have hp : (1 - 2 * (1 / (2 * g)) * v) / (2 * (1 / (2 * g)) ^ 2) =
      2 * g * (g - v) := by field_simp
  have hq : -u / (2 * (1 / (2 * g)) ^ 2) = -2 * g ^ 2 * u := by field_simp
  have hD (t : ℝ) : 1 / (2 * g) * t ^ 2 = t ^ 2 / (2 * g) := by ring
  calc
    Metric.infDist X (focusDirectrixParabola F (line A B)) =
        Metric.infDist (e X) (parabola !₂[f, g / 2] (1 / (2 * g))) := by
      rw [focusDirectrixParabola_eq_vertex_image F A B hAB hF, infDist_isometric_image]
      rfl
    _ = _ := by
      have h := point_parabola_distance (e X) !₂[f, g / 2] (1 / (2 * g)) ha
      have hu : (e X) 0 - (!₂[f, g / 2] : Point2D) 0 = u := rfl
      have hv : (e X) 1 - (!₂[f, g / 2] : Point2D) 1 = v := rfl
      simpa only [hu, hv, hp, hq, hD] using h

end
end SympyGeometry
