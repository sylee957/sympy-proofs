module

public import SympyProofs.Geometry.Circumcenter
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The evolute of a plane curve

The evolute of a plane curve is the locus of its centres of curvature. The
definition here is geometric and uses only points and distances. The formulas
of differential geometry are then theorems about it.

**The definition.** `circumcenters T`, from `SympyProofs.Geometry.Circumcenter`,
is the set of centres of circles through three distinct points of `T`.
`IsLimitCircumcenter S P X`: three points of the set `S` tend to `P`, and the
centre of the circle through them tends to `X`. Such a limit is unique.
`evolute S` is the set of these limits at the points of `S`.

**The formula.** For a parametrized curve `γ` with velocity `γ'` and acceleration
`γ''`, `centerOfCurvature γ t` is

`γ t + (‖γ'‖² / (γ'₀ γ''₁ - γ'₁ γ''₀)) • (-γ'₁, γ'₀)`,

which is `γ + N / κ` for the unit normal `N` and the curvature `κ`.
`isLimitCircumcenter_iff_centerOfCurvature`: for a twice continuously
differentiable curve with nonzero curvature at `t`, the limit of the circle
centres at `γ t` is this point. The hypothesis `IsSimpleAt γ t` says that near
`γ t` the curve is only its arc around the parameter `t`, so that points of the
curve near `γ t` come from parameters near `t`. `evolute_range_eq` is the
resulting description of the evolute of the image of `γ`.

**The osculating circle.** `centerOfCurvature_eq_iff_osculating`: the formula
gives the only point whose squared distance to the curve has vanishing first and
second derivatives at `t`, the centre of the circle with second-order contact.
`isLimitCircumcenter_iff_osculating` states this for the limit of circle centres.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open scoped InnerProductSpace

/-! ### Coordinates in the plane -/

theorem point_eq_iff (U V : Point2D) : U = V ↔ U 0 = V 0 ∧ U 1 = V 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

theorem inner_eq_coordinates (U V : Point2D) : ⟪U, V⟫_ℝ = U 0 * V 0 + U 1 * V 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem norm_sq_eq_coordinates (U : Point2D) : ‖U‖ ^ 2 = U 0 ^ 2 + U 1 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-! ### The evolute, from circles through three points -/

/-- `X` is the limit of the centres of the circles through three points of `S`, as the
three points tend to `P`: such circles exist arbitrarily near `P`, and their centres are
as close to `X` as wanted once the points are close enough to `P`. -/
def IsLimitCircumcenter (S : Set Point2D) (P X : Point2D) : Prop :=
  (∀ δ > 0, (circumcenters (S ∩ Metric.ball P δ)).Nonempty) ∧
    ∀ ε > 0, ∃ δ > 0, circumcenters (S ∩ Metric.ball P δ) ⊆ Metric.ball X ε

/-- The limit of the circle centres is unique. -/
theorem IsLimitCircumcenter.unique {S : Set Point2D} {P X X' : Point2D}
    (h : IsLimitCircumcenter S P X) (h' : IsLimitCircumcenter S P X') : X = X' := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, hX⟩ := h.2 (ε / 2) (half_pos hε)
  obtain ⟨δ', hδ', hX'⟩ := h'.2 (ε / 2) (half_pos hε)
  obtain ⟨Y, hY⟩ := h.1 (min δ δ') (lt_min hδ hδ')
  have hYX : dist Y X < ε / 2 := hX (circumcenters_mono
    (Set.inter_subset_inter_right S (Metric.ball_subset_ball (min_le_left δ δ'))) hY)
  have hYX' : dist Y X' < ε / 2 := hX' (circumcenters_mono
    (Set.inter_subset_inter_right S (Metric.ball_subset_ball (min_le_right δ δ'))) hY)
  calc dist X X' ≤ dist X Y + dist Y X' := dist_triangle _ _ _
    _ ≤ ε := by rw [dist_comm X Y]; linarith

/-- The evolute of a set of points: the limits of circle centres at its points. -/
def evolute (S : Set Point2D) : Set Point2D :=
  {X | ∃ P ∈ S, IsLimitCircumcenter S P X}

theorem mem_evolute_iff (S : Set Point2D) (X : Point2D) :
    X ∈ evolute S ↔ ∃ P ∈ S, IsLimitCircumcenter S P X :=
  Iff.rfl

/-! ### The formula for the centre of curvature -/

/-- The cross product of velocity and acceleration, `x' y'' - y' x''`. It is the
signed curvature times the cube of the speed. -/
def velocityCrossAcceleration (γ : ℝ → Point2D) (t : ℝ) : ℝ :=
  deriv γ t 0 * deriv (deriv γ) t 1 - deriv γ t 1 * deriv (deriv γ) t 0

/-- The centre of curvature of `γ` at `t`, by the formula of differential geometry.
It is meaningful where `velocityCrossAcceleration γ t ≠ 0`. -/
def centerOfCurvature (γ : ℝ → Point2D) (t : ℝ) : Point2D :=
  γ t +
    (‖deriv γ t‖ ^ 2 / velocityCrossAcceleration γ t) • !₂[-deriv γ t 1, deriv γ t 0]

/-- Near `γ t` the curve is only its arc around the parameter `t`: every point of the
curve close to `γ t` is at a parameter close to `t`. This excludes another branch of the
curve passing through `γ t` or accumulating there. -/
def IsSimpleAt (γ : ℝ → Point2D) (t : ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∀ s, dist (γ s) (γ t) < δ → ∃ s', |s' - t| < η ∧ γ s' = γ s

private theorem rolle {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) {a b : ℝ}
    (hab : a < b) (h : g a = g b) : ∃ ξ ∈ Set.Ioo a b, g' ξ = 0 :=
  exists_hasDerivAt_eq_zero hab
    (continuous_iff_continuousAt.mpr fun s => (hg s).continuousAt).continuousOn h
    fun x _ => hg x

/-- Three equal values give a zero of the first derivative and, after it, a zero of the
second. -/
private theorem rolle_three {g g' g'' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    (hg' : ∀ s, HasDerivAt g' (g'' s) s) {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (h₁ : g a = g b) (h₂ : g b = g c) :
    ∃ ξ₁ ∈ Set.Ioo a b, ∃ ξ ∈ Set.Ioo ξ₁ c, g' ξ₁ = 0 ∧ g'' ξ = 0 := by
  obtain ⟨ξ₁, hξ₁, h1⟩ := rolle hg hab h₁
  obtain ⟨ξ₂, hξ₂, h2⟩ := rolle hg hbc h₂
  obtain ⟨ξ, hξ, h3⟩ := rolle hg' (hξ₁.2.trans hξ₂.1) (h1.trans h2.symm)
  exact ⟨ξ₁, hξ₁, ξ, ⟨hξ.1, hξ.2.trans hξ₂.2⟩, h1, h3⟩

private theorem hasDerivAt_dist_sq (γ : ℝ → Point2D) (X : Point2D) (hγ : Differentiable ℝ γ)
    (s : ℝ) :
    HasDerivAt (fun s => dist (γ s) X ^ 2) (2 * ⟪γ s - X, deriv γ s⟫_ℝ) s := by
  simpa only [dist_eq_norm] using ((hγ s).hasDerivAt.sub_const X).norm_sq

private theorem hasDerivAt_inner_deriv (γ : ℝ → Point2D) (X : Point2D)
    (hγ : Differentiable ℝ γ) (s : ℝ) (hγ' : DifferentiableAt ℝ (deriv γ) s) :
    HasDerivAt (fun s => 2 * ⟪γ s - X, deriv γ s⟫_ℝ)
      (2 * (⟪γ s - X, deriv (deriv γ) s⟫_ℝ + ⟪deriv γ s, deriv γ s⟫_ℝ)) s :=
  (((hγ s).hasDerivAt.sub_const X).inner ℝ hγ'.hasDerivAt).const_mul 2

private theorem hasDerivAt_coord (γ : ℝ → Point2D) (hγ : Differentiable ℝ γ) (i : Fin 2)
    (s : ℝ) : HasDerivAt (fun s => γ s i) (deriv γ s i) s :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt s (hγ s).hasDerivAt

/-- The determinant of the two linear conditions "`Y - γ u` is normal to the velocity at
`u`" and "`Y` satisfies the second-order condition at `v`". At `u = v = t` it is
`velocityCrossAcceleration γ t`. -/
private def contactDet (γ : ℝ → Point2D) (p : ℝ × ℝ) : ℝ :=
  deriv γ p.1 0 * deriv (deriv γ) p.2 1 - deriv γ p.1 1 * deriv (deriv γ) p.2 0

private def contactRhs₁ (γ : ℝ → Point2D) (p : ℝ × ℝ) : ℝ :=
  γ p.1 0 * deriv γ p.1 0 + γ p.1 1 * deriv γ p.1 1

private def contactRhs₂ (γ : ℝ → Point2D) (p : ℝ × ℝ) : ℝ :=
  γ p.2 0 * deriv (deriv γ) p.2 0 + γ p.2 1 * deriv (deriv γ) p.2 1 +
    (deriv γ p.2 0 ^ 2 + deriv γ p.2 1 ^ 2)

/-- The solution of the two conditions by Cramer's rule, first coordinate. -/
private def contactX (γ : ℝ → Point2D) (p : ℝ × ℝ) : ℝ :=
  (contactRhs₁ γ p * deriv (deriv γ) p.2 1 - contactRhs₂ γ p * deriv γ p.1 1) /
    contactDet γ p

/-- The solution of the two conditions by Cramer's rule, second coordinate. -/
private def contactY (γ : ℝ → Point2D) (p : ℝ × ℝ) : ℝ :=
  (deriv γ p.1 0 * contactRhs₂ γ p - deriv (deriv γ) p.2 0 * contactRhs₁ γ p) /
    contactDet γ p

private theorem continuous_contactDet (γ : ℝ → Point2D) (hγ' : Differentiable ℝ (deriv γ))
    (hγ'' : Continuous (deriv (deriv γ))) : Continuous (contactDet γ) := by
  have hγ'c : Continuous (deriv γ) := hγ'.continuous
  unfold contactDet
  fun_prop

/-- Near `t`, velocity at one parameter and acceleration at another stay independent. -/
private theorem exists_contactDet_ne_zero (γ : ℝ → Point2D) (t : ℝ)
    (hγ' : Differentiable ℝ (deriv γ)) (hγ'' : Continuous (deriv (deriv γ)))
    (hκ : velocityCrossAcceleration γ t ≠ 0) :
    ∃ δ > 0, ∀ u v : ℝ, |u - t| < δ → |v - t| < δ → contactDet γ (u, v) ≠ 0 := by
  have hκ' : contactDet γ (t, t) ≠ 0 := hκ
  obtain ⟨δ, hδ, hne⟩ := Metric.eventually_nhds_iff.mp
    ((continuous_contactDet γ hγ' hγ'').continuousAt.eventually_ne hκ')
  refine ⟨δ, hδ, fun u v hu hv => hne ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt hu hv

private theorem eq_contact_of_conditions (γ : ℝ → Point2D) (u v : ℝ) (Y : Point2D)
    (h₁ : ⟪γ u - Y, deriv γ u⟫_ℝ = 0)
    (h₂ : ⟪γ v - Y, deriv (deriv γ) v⟫_ℝ + ⟪deriv γ v, deriv γ v⟫_ℝ = 0)
    (hD : contactDet γ (u, v) ≠ 0) :
    Y 0 = contactX γ (u, v) ∧ Y 1 = contactY γ (u, v) := by
  simp only [inner_eq_coordinates, PiLp.sub_apply] at h₁ h₂
  unfold contactX contactY
  constructor
  · rw [eq_div_iff hD]
    dsimp only [contactDet, contactRhs₁, contactRhs₂]
    linear_combination -(deriv (deriv γ) v 1) * h₁ + deriv γ u 1 * h₂
  · rw [eq_div_iff hD]
    dsimp only [contactDet, contactRhs₁, contactRhs₂]
    linear_combination deriv (deriv γ) v 0 * h₁ - deriv γ u 0 * h₂

private theorem contact_self (γ : ℝ → Point2D) (t : ℝ)
    (hκ : velocityCrossAcceleration γ t ≠ 0) :
    contactX γ (t, t) = centerOfCurvature γ t 0 ∧
      contactY γ (t, t) = centerOfCurvature γ t 1 := by
  unfold velocityCrossAcceleration at hκ
  simp only [contactX, contactY, contactDet, contactRhs₁, contactRhs₂, centerOfCurvature,
    velocityCrossAcceleration, norm_sq_eq_coordinates, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  set x := γ t 0
  set y := γ t 1
  set x' := deriv γ t 0
  set y' := deriv γ t 1
  set x'' := deriv (deriv γ) t 0
  set y'' := deriv (deriv γ) t 1
  have key : ∀ {N c n v : ℝ}, N = c * (x' * y'' - y' * x'') + n * v →
      N / (x' * y'' - y' * x'') = c + n / (x' * y'' - y' * x'') * v := by
    intro N c n v h
    rw [h]
    field_simp
  constructor
  · refine key ?_
    ring
  · refine key ?_
    ring

/-- **Circles through three points, by parameters.** For a twice continuously
differentiable curve with nonzero curvature at `t`, a point equidistant from three
points of the curve at increasing parameters near `t` is near the centre of curvature. -/
theorem centerOfCurvature_limit_circumcenter (γ : ℝ → Point2D) (t : ℝ)
    (hγ : Differentiable ℝ γ) (hγ' : Differentiable ℝ (deriv γ))
    (hγ'' : Continuous (deriv (deriv γ))) (hκ : velocityCrossAcceleration γ t ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ s₁ s₂ s₃ : ℝ, ∀ Y : Point2D,
      t - δ < s₁ → s₁ < s₂ → s₂ < s₃ → s₃ < t + δ →
        IsEquidistant Y (γ s₁) (γ s₂) (γ s₃) → dist Y (centerOfCurvature γ t) < ε := by
  intro ε hε
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ'.continuous
  have hκ' : contactDet γ (t, t) ≠ 0 := hκ
  have hDc := continuous_contactDet γ hγ' hγ''
  have hXc : ContinuousAt (contactX γ) (t, t) := by
    unfold contactX
    refine ContinuousAt.div ?_ hDc.continuousAt hκ'
    unfold contactRhs₁ contactRhs₂
    fun_prop
  have hYc : ContinuousAt (contactY γ) (t, t) := by
    unfold contactY
    refine ContinuousAt.div ?_ hDc.continuousAt hκ'
    unfold contactRhs₁ contactRhs₂
    fun_prop
  obtain ⟨δ₀, hδ₀, hne⟩ := exists_contactDet_ne_zero γ t hγ' hγ'' hκ
  obtain ⟨δ₁, hδ₁, hX⟩ := Metric.continuousAt_iff.mp hXc (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hY⟩ := Metric.continuousAt_iff.mp hYc (ε / 2) (half_pos hε)
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂),
    fun s₁ s₂ s₃ Y hs₁ h12 h23 hs₃ ⟨e12, e23⟩ => ?_⟩
  -- Rolle's theorem: the squared distance to `Y` takes one value at three parameters.
  obtain ⟨ξ₁, hξ₁, ξ, hξ, h1, h3⟩ := rolle_three (hasDerivAt_dist_sq γ Y hγ)
    (fun s => hasDerivAt_inner_deriv γ Y hγ s (hγ' s)) h12 h23
    (by rw [dist_comm (γ s₁) Y, dist_comm (γ s₂) Y, e12])
    (by rw [dist_comm (γ s₂) Y, dist_comm (γ s₃) Y, e23])
  -- The two conditions determine `Y`, continuously in the parameters.
  have hδ₀' := min_le_left δ₀ (min δ₁ δ₂)
  have hδ₁' := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂)
  have hδ₂' := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂)
  have hu : |ξ₁ - t| < min δ₀ (min δ₁ δ₂) :=
    abs_lt.mpr ⟨by linarith [hξ₁.1], by linarith [hξ₁.2]⟩
  have hv : |ξ - t| < min δ₀ (min δ₁ δ₂) :=
    abs_lt.mpr ⟨by linarith [hξ₁.1, hξ.1], by linarith [hξ.2]⟩
  have hdist : dist (ξ₁, ξ) (t, t) < min δ₀ (min δ₁ δ₂) := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hu hv
  obtain ⟨hY0, hY1⟩ := eq_contact_of_conditions γ ξ₁ ξ Y (by linarith) (by linarith)
    (hne ξ₁ ξ (hu.trans_le hδ₀') (hv.trans_le hδ₀'))
  obtain ⟨hc0, hc1⟩ := contact_self γ t hκ
  have hx := hX (hdist.trans_le hδ₁')
  have hy := hY (hdist.trans_le hδ₂')
  rw [Real.dist_eq, ← hY0, hc0, abs_lt] at hx
  rw [Real.dist_eq, ← hY1, hc1, abs_lt] at hy
  rw [point_distance_coordinates, Real.sqrt_lt' hε, pointDistanceSq]
  nlinarith [sq_lt_sq' hx.1 hx.2, sq_lt_sq' hy.1 hy.2]

/-- Near a point of nonzero curvature there are three distinct points of the curve, as
close as wanted, with a circle through them. -/
private theorem exists_circumcenter_near (γ : ℝ → Point2D) (t : ℝ) (hγ : Differentiable ℝ γ)
    (hγ' : Differentiable ℝ (deriv γ)) (hγ'' : Continuous (deriv (deriv γ)))
    (hκ : velocityCrossAcceleration γ t ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₁ s₂ s₃ : ℝ, ∃ Y : Point2D,
      dist (γ s₁) (γ t) < δ ∧ dist (γ s₂) (γ t) < δ ∧ dist (γ s₃) (γ t) < δ ∧
        IsCircumcenter Y (γ s₁) (γ s₂) (γ s₃) := by
  obtain ⟨δ₀, hδ₀, hne⟩ := exists_contactDet_ne_zero γ t hγ' hγ'' hκ
  obtain ⟨η, hη, hnear⟩ := Metric.continuousAt_iff.mp (hγ.continuous.continuousAt (x := t)) δ hδ
  -- Linear functions of the point of the curve, and their two derivatives.
  have hlin : ∀ (α β s : ℝ), HasDerivAt (fun s => α * γ s 0 + β * γ s 1)
      (α * deriv γ s 0 + β * deriv γ s 1) s := fun α β s =>
    ((hasDerivAt_coord γ hγ 0 s).const_mul α).add ((hasDerivAt_coord γ hγ 1 s).const_mul β)
  have hlin' : ∀ (α β s : ℝ), HasDerivAt (fun s => α * deriv γ s 0 + β * deriv γ s 1)
      (α * deriv (deriv γ) s 0 + β * deriv (deriv γ) s 1) s := fun α β s =>
    ((hasDerivAt_coord (deriv γ) hγ' 0 s).const_mul α).add
      ((hasDerivAt_coord (deriv γ) hγ' 1 s).const_mul β)
  -- Distinct parameters just after `t` give distinct points.
  have hinj : ∀ a b : ℝ, t ≤ a → a < b → b < t + δ₀ → γ a ≠ γ b := by
    intro a b ha hab hb heq
    obtain ⟨ξ, hξ, h⟩ := rolle (hlin (-(deriv (deriv γ) t 1)) (deriv (deriv γ) t 0)) hab
      (by beta_reduce; rw [heq])
    refine hne ξ t (abs_lt.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
      (by rw [sub_self, abs_zero]; exact hδ₀) ?_
    dsimp only [contactDet]
    linear_combination -h
  have hw : 0 < min η δ₀ := lt_min hη hδ₀
  have hwη : min η δ₀ ≤ η := min_le_left _ _
  have hwδ : min η δ₀ ≤ δ₀ := min_le_right _ _
  have h12 : t < t + min η δ₀ / 3 := by linarith
  have h23 : t + min η δ₀ / 3 < t + 2 * min η δ₀ / 3 := by linarith
  have n12 := hinj t (t + min η δ₀ / 3) le_rfl h12 (by linarith)
  have n23 := hinj (t + min η δ₀ / 3) (t + 2 * min η δ₀ / 3) h12.le h23 (by linarith)
  have n13 := hinj t (t + 2 * min η δ₀ / 3) le_rfl (h12.trans h23) (by linarith)
  -- Three such points are not on a line.
  have hΔ : (γ (t + min η δ₀ / 3) 0 - γ t 0) *
        (γ (t + 2 * min η δ₀ / 3) 1 - γ (t + min η δ₀ / 3) 1) -
      (γ (t + min η δ₀ / 3) 1 - γ t 1) *
        (γ (t + 2 * min η δ₀ / 3) 0 - γ (t + min η δ₀ / 3) 0) ≠ 0 := by
    intro hΔ
    obtain ⟨ξ₁, hξ₁, ξ, hξ, h1, h2⟩ := rolle_three
      (hlin (-(γ (t + min η δ₀ / 3) 1 - γ t 1)) (γ (t + min η δ₀ / 3) 0 - γ t 0))
      (hlin' (-(γ (t + min η δ₀ / 3) 1 - γ t 1)) (γ (t + min η δ₀ / 3) 0 - γ t 0)) h12 h23
      (by beta_reduce; ring) (by beta_reduce; linear_combination -hΔ)
    have hD := hne ξ₁ ξ (abs_lt.mpr ⟨by linarith [hξ₁.1], by linarith [hξ₁.2]⟩)
      (abs_lt.mpr ⟨by linarith [hξ₁.1, hξ.1], by linarith [hξ.2]⟩)
    dsimp only [contactDet] at hD
    beta_reduce at h1 h2
    have hα : -(γ (t + min η δ₀ / 3) 1 - γ t 1) *
        (deriv γ ξ₁ 0 * deriv (deriv γ) ξ 1 - deriv γ ξ₁ 1 * deriv (deriv γ) ξ 0) = 0 := by
      linear_combination deriv (deriv γ) ξ 1 * h1 - deriv γ ξ₁ 1 * h2
    have hβ : (γ (t + min η δ₀ / 3) 0 - γ t 0) *
        (deriv γ ξ₁ 0 * deriv (deriv γ) ξ 1 - deriv γ ξ₁ 1 * deriv (deriv γ) ξ 0) = 0 := by
      linear_combination deriv γ ξ₁ 0 * h2 - deriv (deriv γ) ξ 0 * h1
    have hα' := (mul_eq_zero.mp hα).resolve_right hD
    have hβ' := (mul_eq_zero.mp hβ).resolve_right hD
    exact n12 ((point_eq_iff _ _).mpr ⟨by linarith, by linarith⟩)
  obtain ⟨Y, hY⟩ := exists_equidistant _ _ _ hΔ
  refine ⟨t, t + min η δ₀ / 3, t + 2 * min η δ₀ / 3, Y, ?_, ?_, ?_, n12, n23, n13, hY⟩
  · rw [dist_self]
    exact hδ
  · refine hnear ?_
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith
  · refine hnear ?_
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith

/-- **The limit of circle centres is the centre of curvature.** For a twice continuously
differentiable curve with nonzero curvature at `t`, simple at `t`, the centres of the
circles through three points of the curve tending to `γ t` tend to
`centerOfCurvature γ t`, and to no other point. -/
theorem isLimitCircumcenter_iff_centerOfCurvature (γ : ℝ → Point2D) (t : ℝ) (X : Point2D)
    (hγ : Differentiable ℝ γ) (hγ' : Differentiable ℝ (deriv γ))
    (hγ'' : Continuous (deriv (deriv γ))) (hκ : velocityCrossAcceleration γ t ≠ 0)
    (hs : IsSimpleAt γ t) :
    IsLimitCircumcenter (Set.range γ) (γ t) X ↔ centerOfCurvature γ t = X := by
  have key : IsLimitCircumcenter (Set.range γ) (γ t) (centerOfCurvature γ t) := by
    constructor
    · intro δ hδ
      obtain ⟨s₁, s₂, s₃, Y, d₁, d₂, d₃, hY⟩ :=
        exists_circumcenter_near γ t hγ hγ' hγ'' hκ δ hδ
      exact ⟨Y, γ s₁, ⟨⟨s₁, rfl⟩, d₁⟩, γ s₂, ⟨⟨s₂, rfl⟩, d₂⟩, γ s₃, ⟨⟨s₃, rfl⟩, d₃⟩, hY⟩
    · intro ε hε
      obtain ⟨δ', hδ', hlim⟩ := centerOfCurvature_limit_circumcenter γ t hγ hγ' hγ'' hκ ε hε
      obtain ⟨δ, hδ, hcover⟩ := hs δ' hδ'
      refine ⟨δ, hδ, ?_⟩
      rintro Y ⟨_, ⟨⟨u₁, rfl⟩, d₁⟩, _, ⟨⟨u₂, rfl⟩, d₂⟩, _, ⟨⟨u₃, rfl⟩, d₃⟩, n12, n23, n13,
        e12, e23⟩
      rw [Metric.mem_ball]
      obtain ⟨s₁, hs₁, h₁⟩ := hcover u₁ d₁
      obtain ⟨s₂, hs₂, h₂⟩ := hcover u₂ d₂
      obtain ⟨s₃, hs₃, h₃⟩ := hcover u₃ d₃
      rw [← h₁, ← h₂] at n12 e12
      rw [← h₂, ← h₃] at n23 e23
      rw [← h₁, ← h₃] at n13
      have m12 : s₁ ≠ s₂ := fun h => n12 (by rw [h])
      have m23 : s₂ ≠ s₃ := fun h => n23 (by rw [h])
      have m13 : s₁ ≠ s₃ := fun h => n13 (by rw [h])
      have core : ∀ a b c : ℝ, |a - t| < δ' → |c - t| < δ' → a < b → b < c →
          dist Y (γ a) = dist Y (γ b) → dist Y (γ b) = dist Y (γ c) →
          dist Y (centerOfCurvature γ t) < ε := fun a b c ha hc hab hbc e e' =>
        hlim a b c Y (by linarith [(abs_lt.mp ha).1]) hab hbc (by linarith [(abs_lt.mp hc).2])
          ⟨e, e'⟩
      have e13 := e12.trans e23
      rcases lt_or_gt_of_ne m12 with l12 | l12 <;> rcases lt_or_gt_of_ne m23 with l23 | l23
      · exact core s₁ s₂ s₃ hs₁ hs₃ l12 l23 e12 e23
      · rcases lt_or_gt_of_ne m13 with l13 | l13
        · exact core s₁ s₃ s₂ hs₁ hs₂ l13 l23 e13 e23.symm
        · exact core s₃ s₁ s₂ hs₃ hs₂ l13 l12 e13.symm e12
      · rcases lt_or_gt_of_ne m13 with l13 | l13
        · exact core s₂ s₁ s₃ hs₂ hs₃ l12 l13 e12.symm e13
        · exact core s₂ s₃ s₁ hs₂ hs₁ l23 l13 e23 e13.symm
      · exact core s₃ s₂ s₁ hs₃ hs₁ l23 l12 e23.symm e12.symm
  exact ⟨fun h => key.unique h, by rintro rfl; exact key⟩

/-- The evolute of the image of a curve is the image of the formula, when the curve is
twice continuously differentiable, of nonzero curvature and simple at every parameter. -/
theorem evolute_range_eq (γ : ℝ → Point2D) (hγ : Differentiable ℝ γ)
    (hγ' : Differentiable ℝ (deriv γ)) (hγ'' : Continuous (deriv (deriv γ)))
    (hκ : ∀ t, velocityCrossAcceleration γ t ≠ 0) (hs : ∀ t, IsSimpleAt γ t) :
    evolute (Set.range γ) = Set.range (centerOfCurvature γ) := by
  ext X
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, hX⟩
    exact ⟨t, (isLimitCircumcenter_iff_centerOfCurvature γ t X hγ hγ' hγ'' (hκ t)
      (hs t)).mp hX⟩
  · rintro ⟨t, rfl⟩
    exact ⟨γ t, ⟨t, rfl⟩, (isLimitCircumcenter_iff_centerOfCurvature γ t _ hγ hγ' hγ''
      (hκ t) (hs t)).mpr rfl⟩

/-! ### The osculating circle -/

/-- The formula gives the centre of the osculating circle: it is the only point `X` for
which the squared distance from `X` to the curve is stationary to second order at `t`. -/
theorem centerOfCurvature_eq_iff_osculating (γ : ℝ → Point2D) (t : ℝ) (X : Point2D)
    (hγ : Differentiable ℝ γ) (hγ' : DifferentiableAt ℝ (deriv γ) t)
    (hκ : velocityCrossAcceleration γ t ≠ 0) :
    centerOfCurvature γ t = X ↔
      deriv (fun s => dist (γ s) X ^ 2) t = 0 ∧
        deriv (deriv fun s => dist (γ s) X ^ 2) t = 0 := by
  have hderiv : (deriv fun s => dist (γ s) X ^ 2) =
      fun s => 2 * ⟪γ s - X, deriv γ s⟫_ℝ :=
    funext fun s => (hasDerivAt_dist_sq γ X hγ s).deriv
  rw [hderiv, (hasDerivAt_inner_deriv γ X hγ t hγ').deriv, point_eq_iff]
  unfold centerOfCurvature
  unfold velocityCrossAcceleration at hκ ⊢
  simp only [inner_eq_coordinates, norm_sq_eq_coordinates, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  set x := γ t 0
  set y := γ t 1
  set x' := deriv γ t 0
  set y' := deriv γ t 1
  set x'' := deriv (deriv γ) t 0
  set y'' := deriv (deriv γ) t 1
  constructor
  · rintro ⟨h0, h1⟩
    rw [← h0, ← h1]
    constructor
    · field_simp
      ring
    · field_simp
      ring
  · rintro ⟨h0, h1⟩
    constructor
    · field_simp
      linear_combination (y'' / 2) * h0 - (y' / 2) * h1
    · field_simp
      linear_combination (x' / 2) * h1 - (x'' / 2) * h0

/-- The limit of circle centres is the centre of the osculating circle. -/
theorem isLimitCircumcenter_iff_osculating (γ : ℝ → Point2D) (t : ℝ) (X : Point2D)
    (hγ : Differentiable ℝ γ) (hγ' : Differentiable ℝ (deriv γ))
    (hγ'' : Continuous (deriv (deriv γ))) (hκ : velocityCrossAcceleration γ t ≠ 0)
    (hs : IsSimpleAt γ t) :
    IsLimitCircumcenter (Set.range γ) (γ t) X ↔
      deriv (fun s => dist (γ s) X ^ 2) t = 0 ∧
        deriv (deriv fun s => dist (γ s) X ^ 2) t = 0 := by
  rw [isLimitCircumcenter_iff_centerOfCurvature γ t X hγ hγ' hγ'' hκ hs,
    centerOfCurvature_eq_iff_osculating γ t X hγ (hγ' t) hκ]

end

end SympyGeometry
