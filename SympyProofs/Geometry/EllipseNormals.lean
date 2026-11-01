module

public import SympyProofs.Geometry.PointConicDistance

/-!
# Explicit ellipse normal lines

`ellipse_normal_lines` is a theorem whose statement gives the full formula as
one `let` expression, with names for its mathematical stages. It produces a
fixed twelve-element list of geometric lines using `SympyGeometry.line Q R`.
Each line is constructed from distinct points, starting at a contact point on
the ellipse, and passes through the query. The list contains exactly the ellipse
normals through the query. There is no result wrapper, infinite case constructor,
or exceptional branch in the formula.

The hypotheses are positive semiaxes and `a^2 ≠ b^2 ∨ X ≠ C`, excluding only
a circle queried at its center. Axis queries and multiple roots use the same
Cardano/Ferrari expression. The twelve candidate feet consist of the omitted
rational-chart pole and eleven radical parameters. A sign-based arithmetic
selector replaces surplus candidates by a valid duplicate. The formula has no
Boolean decisions, filters, or conditional expressions.

For an equation `A*x+B*y=D`, let `r=A*X.x+B*X.y-D` and `e=1-sign(r^2)`.
Then `e*L+(1-e)*M`, applied coefficientwise, keeps `L` when it passes through
the query and otherwise gives `M`. Folding this selector over the candidate list
chooses a valid fallback; mapping it replaces invalid candidates by that fallback.
Existence is proved from the stationary polynomial's opposite values at `t=-1`
and `t=1`.

With `u = X.x-C.x`, `v = X.y-C.y`, the stationary parameters are the real roots of
`b*v*t^4 + 2*(a^2+a*u-b^2)*t^3 + 2*(b^2-a^2+a*u)*t - b*v`.
A finite parameter gives centered coordinates
`x = a*(1-t^2)/(1+t^2)`, `y = 2*b*t/(1+t^2)`, and coefficients
`(a^2*y, -b^2*x, a^2*y*(C.x+x)-b^2*x*(C.y+y))`.
The pole gives the horizontal line and survives unchanged exactly when `v = 0`.

The formula uses coefficients `A*x+B*y=D` as intermediates. For these unscaled
normal coefficients, `Q=(C.x-B/b^2, C.y+A/a^2)` recovers the contact point and
`R=Q+(-B,A)` gives a second point. This handles horizontal and vertical normals
without slope cases. The existing `line Q R` primitive represents each line as
a `Set Point2D`; the collection of normals remains a list. The same two points
can be passed to SymPy's `Line2D` constructor.

Existing conic parametrization proofs are reused internally.
Real sign encodes an exact zero test. This noncomputable real-arithmetic formula
does not assert correctness of a floating-point implementation.
-/

@[expose] public section

namespace SympyGeometry

open scoped InnerProductSpace

noncomputable section

/-- Incidence in the equation `A*x + B*y = D`, with three scalar coefficients. -/
def lineHolds (A B D : ℝ) (X : Point2D) : Prop := A * X 0 + B * X 1 = D

namespace EllipseNormals

/-- Arithmetic selection: keep an incident line, otherwise use the fallback. -/
def signPick (X : Point2D) (A B D : ℝ) (fallback : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (A₀, B₀, D₀) := fallback
  let residual := A * X 0 + B * X 1 - D
  let e := 1 - Real.sign (residual ^ 2)
  (e * A + (1 - e) * A₀, e * B + (1 - e) * B₀, e * D + (1 - e) * D₀)

theorem signPick_of_holds (X : Point2D) (A B D : ℝ) (fallback : ℝ × ℝ × ℝ)
    (h : lineHolds A B D X) : signPick X A B D fallback = (A, B, D) := by
  have he : A * X 0 + B * X 1 - D = 0 := sub_eq_zero.mpr h
  simp [signPick, he]

theorem signPick_of_not_holds (X : Point2D) (A B D : ℝ) (fallback : ℝ × ℝ × ℝ)
    (h : ¬ lineHolds A B D X) : signPick X A B D fallback = fallback := by
  have he : A * X 0 + B * X 1 - D ≠ 0 := sub_ne_zero.mpr h
  simp [signPick, Real.sign_of_pos (sq_pos_of_ne_zero he)]

/-- Select the first incident candidate. -/
def signFallback (X : Point2D) (ls : List (ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  ls.foldr (fun (A, B, D) fallback => signPick X A B D fallback) (0, 0, 0)

theorem signFallback_spec (X : Point2D) (ls : List (ℝ × ℝ × ℝ))
    (hne : ∃ L ∈ ls, lineHolds L.1 L.2.1 L.2.2 X) :
    let (A, B, D) := signFallback X ls
    (A, B, D) ∈ ls ∧ lineHolds A B D X := by
  induction ls with
  | nil => obtain ⟨L, hL, _⟩ := hne; simp at hL
  | cons L ls ih =>
    change (let K := signPick X L.1 L.2.1 L.2.2 (signFallback X ls)
      K ∈ L :: ls ∧ lineHolds K.1 K.2.1 K.2.2 X)
    by_cases h : lineHolds L.1 L.2.1 L.2.2 X
    · rw [signPick_of_holds X L.1 L.2.1 L.2.2 _ h]
      exact ⟨List.mem_cons_self, h⟩
    · have htail : ∃ K ∈ ls, lineHolds K.1 K.2.1 K.2.2 X := by
        obtain ⟨K, hK, hX⟩ := hne
        rcases List.mem_cons.mp hK with rfl | hK
        · exact (h hX).elim
        · exact ⟨K, hK, hX⟩
      obtain ⟨hmem, hX⟩ := ih htail
      rw [signPick_of_not_holds X L.1 L.2.1 L.2.2 _ h]
      exact ⟨List.mem_cons_of_mem L hmem, hX⟩

/-- Replace invalid entries by a valid duplicate, preserving the list length. -/
def signRepair (X : Point2D) (ls : List (ℝ × ℝ × ℝ)) : List (ℝ × ℝ × ℝ) :=
  ls.map (fun (A, B, D) => signPick X A B D (signFallback X ls))

theorem mem_signRepair_iff (X : Point2D) (ls : List (ℝ × ℝ × ℝ))
    (hne : ∃ L ∈ ls, lineHolds L.1 L.2.1 L.2.2 X) (K : ℝ × ℝ × ℝ) :
    K ∈ signRepair X ls ↔ K ∈ ls ∧ lineHolds K.1 K.2.1 K.2.2 X := by
  obtain ⟨hfmem, hfX⟩ := signFallback_spec X ls hne
  constructor
  · intro hK
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
    rcases L with ⟨A, B, D⟩
    dsimp only
    by_cases h : lineHolds A B D X
    · rw [signPick_of_holds X A B D _ h]
      exact ⟨hL, h⟩
    · rw [signPick_of_not_holds X A B D _ h]
      exact ⟨hfmem, hfX⟩
  · rintro ⟨hK, hX⟩
    exact List.mem_map.mpr ⟨K, hK, signPick_of_holds X K.1 K.2.1 K.2.2 _ hX⟩

end EllipseNormals

/-- Scalar ellipse equation, with no set-valued representation. -/
def onEllipse (C : Point2D) (a b : ℝ) (Y : Point2D) : Prop :=
  b ^ 2 * (Y 0 - C 0) ^ 2 + a ^ 2 * (Y 1 - C 1) ^ 2 = a ^ 2 * b ^ 2

/-- Half the gradient of the implicit ellipse equation. -/
def ellipseNormalDirection (C Y : Point2D) (a b : ℝ) : Point2D :=
  !₂[b ^ 2 * (Y 0 - C 0), a ^ 2 * (Y 1 - C 1)]

/-- Explicit coefficients of the normal at `Y`; vertical lines need no special case. -/
def ellipseNormalLine (C : Point2D) (a b : ℝ) (Y : Point2D) : ℝ × ℝ × ℝ :=
  let A := a ^ 2 * (Y 1 - C 1)
  let B := -b ^ 2 * (Y 0 - C 0)
  (A, B, A * Y 0 + B * Y 1)

/-- The normal at `Y` passes through `X`. -/
def ellipseNormalThrough (C : Point2D) (a b : ℝ) (Y X : Point2D) : Prop :=
  let (A, B, D) := ellipseNormalLine C a b Y
  lineHolds A B D X

theorem ellipseNormalLine_holds_iff (C X Y : Point2D) (a b : ℝ) :
    ellipseNormalThrough C a b Y X ↔
      a ^ 2 * (Y 1 - C 1) * (X 0 - Y 0) -
        b ^ 2 * (Y 0 - C 0) * (X 1 - Y 1) = 0 := by
  unfold ellipseNormalThrough lineHolds ellipseNormalLine
  constructor <;> intro h <;> linear_combination h

theorem ellipseNormalDirection_ne_zero (C Y : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hY : onEllipse C a b Y) :
    ellipseNormalDirection C Y a b ≠ 0 := by
  intro h
  have hx := congrArg (fun p : Point2D => p 0) h
  have hy := congrArg (fun p : Point2D => p 1) h
  simp only [ellipseNormalDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, PiLp.zero_apply] at hx hy
  have hx0 := (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 hb)
  have hy0 := (mul_eq_zero.mp hy).resolve_left (pow_ne_zero 2 ha)
  have he : a ^ 2 * b ^ 2 = 0 := by
    simpa only [onEllipse, hx0, hy0, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, add_zero] using hY.symm
  exact mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb) he

/-- The normal direction is perpendicular to the velocity of every differentiable curve
on the ellipse. -/
theorem ellipse_normal_perpendicular_velocity (C : Point2D) (a b t : ℝ)
    (γ : ℝ → Point2D) (v : Point2D) (hγ : HasDerivAt γ v t)
    (hcurve : ∀ s, onEllipse C a b (γ s)) :
    ⟪ellipseNormalDirection C (γ t) a b, v⟫_ℝ = 0 := by
  have hf : HasDerivAt (fun s => γ s 0) (v 0) t :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hγ
  have hg : HasDerivAt (fun s => γ s 1) (v 1) t :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt.comp_hasDerivAt t hγ
  have hd := (((hf.sub_const (C 0)).pow 2).const_mul (b ^ 2)).add
    (((hg.sub_const (C 1)).pow 2).const_mul (a ^ 2))
  have he : (fun s => b ^ 2 * (γ s 0 - C 0) ^ 2 + a ^ 2 * (γ s 1 - C 1) ^ 2) =
      (fun _ => a ^ 2 * b ^ 2) := funext hcurve
  change HasDerivAt (fun s => b ^ 2 * (γ s 0 - C 0) ^ 2 + a ^ 2 * (γ s 1 - C 1) ^ 2)
    _ t at hd
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (a ^ 2 * b ^ 2))
  dsimp at hz
  simp [ellipseNormalDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  linear_combination hz / 2

/-- The implicit equation is exactly the affine line in the gradient direction. -/
theorem ellipseNormalLine_holds_iff_param (C X Y : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hY : onEllipse C a b Y) :
    ellipseNormalThrough C a b Y X ↔
      ∃ s : ℝ, X = Y + s • ellipseNormalDirection C Y a b := by
  rw [ellipseNormalLine_holds_iff]
  let nx := b ^ 2 * (Y 0 - C 0)
  let ny := a ^ 2 * (Y 1 - C 1)
  change ny * (X 0 - Y 0) - nx * (X 1 - Y 1) = 0 ↔ _
  constructor
  · intro h
    by_cases hx : nx = 0
    · have hy : ny ≠ 0 := by
        intro hy
        apply ellipseNormalDirection_ne_zero C Y a b ha hb hY
        ext i
        fin_cases i
        · exact hx
        · exact hy
      have he : X 0 = Y 0 := by
        have : ny * (X 0 - Y 0) = 0 := by simpa [hx] using h
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hy)
      refine ⟨(X 1 - Y 1) / ny, ?_⟩
      ext i
      fin_cases i
      · change X 0 = Y 0 + (X 1 - Y 1) / ny * nx
        simp [hx, he]
      · change X 1 = Y 1 + (X 1 - Y 1) / ny * ny
        rw [div_mul_cancel₀ _ hy]; ring
    · refine ⟨(X 0 - Y 0) / nx, ?_⟩
      ext i
      fin_cases i
      · change X 0 = Y 0 + (X 0 - Y 0) / nx * nx
        rw [div_mul_cancel₀ _ hx]; ring
      · change X 1 = Y 1 + (X 0 - Y 0) / nx * ny
        field_simp
        linear_combination -h
  · rintro ⟨s, rfl⟩
    change ny * (Y 0 + s * nx - Y 0) - nx * (Y 1 + s * ny - Y 1) = 0
    ring

/-- Incidence of the normal expressed using the existing geometric line constructor. -/
theorem ellipseNormalThrough_iff_mem_line (C X Y : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hY : onEllipse C a b Y) :
    ellipseNormalThrough C a b Y X ↔
      X ∈ line Y (Y + ellipseNormalDirection C Y a b) := by
  simpa only [mem_line_iff, add_sub_cancel_left, eq_comm] using
    ellipseNormalLine_holds_iff_param C X Y a b ha hb hY

/-- Recover the contact point and a second point from the unscaled normal coefficients.
These are the two distinct-point arguments used by SymPy's `Line2D` constructor. -/
theorem ellipseNormalLine_constructor_points (C Y : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    let (A, B, _) := ellipseNormalLine C a b Y
    let px := C 0 - B / b ^ 2
    let py := C 1 + A / a ^ 2
    ((!₂[px, py] : Point2D), (!₂[px - B, py + A] : Point2D)) =
      (Y, Y + ellipseNormalDirection C Y a b) := by
  dsimp [ellipseNormalLine, ellipseNormalDirection]
  ext i <;> fin_cases i <;> simp <;> field_simp <;> ring

private theorem ellipse_param_denom (t : ℝ) : 1 + t ^ 2 ≠ 0 := by positivity

theorem ellipsePoint_onEllipse (C : Point2D) (a b t : ℝ) :
    onEllipse C a b (conicPoint C a b 1 t) := by
  have hd := ellipse_param_denom t
  simp only [onEllipse, conicPoint, PiLp.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, add_sub_cancel_left]
  field_simp
  ring

/-- Exact quartic reduction, with neither squaring nor a coordinate sign choice. -/
theorem ellipse_normal_param_iff (C X : Point2D) (a b t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseNormalThrough C a b (conicPoint C a b 1 t) X ↔
      conicStationary a b 1 (X 0 - C 0) (X 1 - C 1) t = 0 := by
  rw [ellipseNormalLine_holds_iff]
  have hd := ellipse_param_denom t
  have hid :
      a ^ 2 * (2 * b * t / (1 + t ^ 2)) *
          (X 0 - (C 0 + a * (1 - t ^ 2) / (1 + t ^ 2))) -
        b ^ 2 * (a * (1 - t ^ 2) / (1 + t ^ 2)) *
          (X 1 - (C 1 + 2 * b * t / (1 + t ^ 2))) =
        a * b / (1 + t ^ 2) ^ 2 *
          conicStationary a b 1 (X 0 - C 0) (X 1 - C 1) t := by
    unfold conicStationary
    field_simp
    ring
  simp only [conicPoint, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul, add_sub_cancel_left]
  rw [hid, mul_eq_zero]
  exact or_iff_right (div_ne_zero (mul_ne_zero ha hb) (pow_ne_zero 2 hd))

theorem ellipse_normal_pole_iff (C X : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ellipseNormalThrough C a b (conicPole C a) X ↔ X 1 = C 1 := by
  rw [ellipseNormalLine_holds_iff]
  simp only [conicPole, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hn : b ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hb) ha
  have he : a ^ 2 * (C 1 + 0 - C 1) * (X 0 - (C 0 + -a)) -
      b ^ 2 * (C 0 + -a - C 0) * (X 1 - (C 1 + 0)) =
      (b ^ 2 * a) * (X 1 - C 1) := by ring
  rw [he, mul_eq_zero, or_iff_right hn, sub_eq_zero]

/-- One radical expression for the eleven finite parameter candidates. All square
and cube roots are fixed complex roots. `radicalInv` is the sign-based reciprocal
that is zero at zero; `monicCubicRoot` is the explicit Cardano expression.
The quadratic and biquadratic entries cover vanishing quartic coefficients
without additional exceptional branches. -/
def ellipseNormalParameters (A B D : ℝ) : List ℝ :=
  let α := (B : ℂ) * radicalInv A
  let δ := (D : ℂ) * radicalInv A
  let p := -3 * α ^ 2 / 8
  let q := α ^ 3 / 8 + δ
  let r := -3 * α ^ 4 / 256 - α * δ / 4 - 1
  let z := monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2)
  let s := sqrtC z
  let u := sqrtC (-2 * p - z + 2 * q * radicalInv s)
  let v := sqrtC (-2 * p - z - 2 * q * radicalInv s)
  let w := sqrtC (p ^ 2 - 4 * r)
  let k := sqrtC (-(D : ℂ) * radicalInv B)
  [0, k.re, (-k).re,
    ((-s + u) / 2 - α / 4).re, ((-s - u) / 2 - α / 4).re,
    ((s + v) / 2 - α / 4).re, ((s - v) / 2 - α / 4).re,
    (sqrtC ((-p + w) / 2) - α / 4).re, (-sqrtC ((-p + w) / 2) - α / 4).re,
    (sqrtC ((-p - w) / 2) - α / 4).re, (-sqrtC ((-p - w) / 2) - α / 4).re]

theorem ellipseNormalParameters_eq_sparse (A B D : ℝ) :
    ellipseNormalParameters A B D = sparseQuarticRadicals A B D := by
  simp [ellipseNormalParameters, sparseQuarticRadicals, quarticRadicals,
    depressedQuarticRadicals, neg_div, sub_eq_add_neg]

/-- Explicit radical candidates, including the point omitted by the rational chart. -/
def ellipseNormalCandidates (X C : Point2D) (a b : ℝ) : List Point2D :=
  conicPole C a ::
    (ellipseNormalParameters (b * (X 1 - C 1))
      (2 * (a ^ 2 + a * (X 0 - C 0) - b ^ 2))
      (2 * (b ^ 2 - a ^ 2 + a * (X 0 - C 0)))).map (conicPoint C a b 1)

theorem ellipseNormalCandidates_mem (X C Y : Point2D) (a b : ℝ)
    (h : Y ∈ ellipseNormalCandidates X C a b) : onEllipse C a b Y := by
  rcases List.mem_cons.mp h with rfl | h
  · simp [onEllipse, conicPole, mul_comm]
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact ellipsePoint_onEllipse C a b t

/-- The only identically zero quartic is the circle queried at its center. -/
theorem ellipse_stationary_coefficients_zero_iff (X C : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (b * (X 1 - C 1) = 0 ∧
      2 * (a ^ 2 + a * (X 0 - C 0) - b ^ 2) = 0 ∧
      2 * (b ^ 2 - a ^ 2 + a * (X 0 - C 0)) = 0) ↔
      a ^ 2 = b ^ 2 ∧ X = C := by
  constructor
  · rintro ⟨hv, hB, hD⟩
    have hy := sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left hb)
    have hx : X 0 = C 0 := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show a * (X 0 - C 0) = 0 by linarith)).resolve_left ha
    exact ⟨by rw [hx] at hB; nlinarith [hB], by ext i; fin_cases i <;> assumption⟩
  · rintro ⟨hab, rfl⟩
    simp [hab]

/-- Soundness and completeness of the finite radical formula, including all axis cases. -/
theorem ellipseNormalCandidates_iff (X C Y : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hn : ¬ (a ^ 2 = b ^ 2 ∧ X = C)) :
    (Y ∈ ellipseNormalCandidates X C a b ∧ ellipseNormalThrough C a b Y X) ↔
      onEllipse C a b Y ∧ ellipseNormalThrough C a b Y X := by
  constructor
  · rintro ⟨hY, hX⟩
    exact ⟨ellipseNormalCandidates_mem X C Y a b hY, hX⟩
  · rintro ⟨hY, hX⟩
    refine ⟨?_, hX⟩
    rcases axisConic_parametrization C Y a b 1 ha hb (Or.inl rfl)
      (by simpa [axisConic, onEllipse] using hY) with
      hp | ⟨t, _, rfl⟩
    · simp [ellipseNormalCandidates, hp]
    · apply List.mem_cons.mpr
      right
      apply List.mem_map.mpr
      refine ⟨t, ?_, rfl⟩
      rw [ellipseNormalParameters_eq_sparse]
      apply mem_sparseQuarticRadicals
      · have h := mt (ellipse_stationary_coefficients_zero_iff X C a b ha hb).mp hn
        tauto
      · simpa only [conicStationary, one_mul] using
          (ellipse_normal_param_iff C X a b t ha hb).mp hX
/-- Raw normal-line equations at the twelve candidate feet. -/
def ellipseNormalRawLines (X C : Point2D) (a b : ℝ) : List (ℝ × ℝ × ℝ) :=
  (ellipseNormalCandidates X C a b).map (ellipseNormalLine C a b)

/-- The geometric construction equals a direct calculation on coordinate pairs. -/
theorem ellipseNormalRawLines_eq_coefficients (X C : Point2D) (a b : ℝ) :
    ellipseNormalRawLines X C a b =
      let ts := ellipseNormalParameters (b * (X 1 - C 1))
        (2 * (a ^ 2 + a * (X 0 - C 0) - b ^ 2))
        (2 * (b ^ 2 - a ^ 2 + a * (X 0 - C 0)))
      let point := fun t : ℝ =>
        let t2 := t ^ 2
        let d := 1 + t2
        (a * (1 - t2) / d, 2 * b * t / d)
      let coefficientsAt := fun xy : ℝ × ℝ =>
        let A := a ^ 2 * xy.2
        let B := -b ^ 2 * xy.1
        (A, B, A * (C 0 + xy.1) + B * (C 1 + xy.2))
      ((-a, 0) :: ts.map point).map coefficientsAt := by
  simp only [ellipseNormalRawLines, ellipseNormalCandidates, List.map_cons,
    List.map_map, Function.comp_def]
  congr 1
  · simp [ellipseNormalLine, conicPole]
  · apply List.map_congr_left
    intro t _
    simp [ellipseNormalLine, conicPoint]

/-- The stationary polynomial has opposite values at `-1` and `1`, hence a real root. -/
private theorem exists_ellipse_stationary (a b u v : ℝ) :
    ∃ t : ℝ, conicStationary a b 1 u v t = 0 := by
  let f := conicStationary a b 1 u v
  have hc : Continuous f := by unfold f conicStationary; fun_prop
  have hm : f (-1) = -(4 * a * u) := by dsimp [f, conicStationary]; ring
  have hp : f 1 = 4 * a * u := by dsimp [f, conicStationary]; ring
  rcases le_total 0 (4 * a * u) with h | h
  · exact intermediate_value_univ (-1) 1 hc (by
      change f (-1) ≤ 0 ∧ 0 ≤ f 1
      rw [hm, hp]
      exact ⟨neg_nonpos.mpr h, h⟩)
  · exact intermediate_value_univ 1 (-1) hc (by
      change f 1 ≤ 0 ∧ 0 ≤ f (-1)
      rw [hp, hm]
      exact ⟨h, neg_nonneg.mpr h⟩)

private theorem ellipseNormalRawLines_incident (X C : Point2D) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hn : ¬ (a ^ 2 = b ^ 2 ∧ X = C)) :
    ∃ L ∈ ellipseNormalRawLines X C a b, lineHolds L.1 L.2.1 L.2.2 X := by
  obtain ⟨t, ht⟩ := exists_ellipse_stationary a b (X 0 - C 0) (X 1 - C 1)
  have hX := (ellipse_normal_param_iff C X a b t ha hb).mpr ht
  refine ⟨ellipseNormalLine C a b (conicPoint C a b 1 t), List.mem_map.mpr ?_, hX⟩
  refine ⟨conicPoint C a b 1 t, ?_, rfl⟩
  exact ((ellipseNormalCandidates_iff X C _ a b ha hb hn).mpr
    ⟨ellipsePoint_onEllipse C a b t, hX⟩).1

/-- Explicit formula for all normals through `X`, organized into the quartic,
Cardano/Ferrari radicals, candidate points, and two-point line construction.
The precondition excludes only a circle queried at its center. Sign-based
selection replaces invalid candidates by valid duplicates. Each resulting `line`
joins a contact point to that point plus the nonzero normal direction.
The list always has twelve entries; `map` and
`foldr` express the repeated arithmetic without numbered temporary variables.
There are no Boolean tests, filters, or conditional expressions. -/
theorem ellipse_normal_lines (X C : Point2D) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : a ^ 2 ≠ b ^ 2 ∨ X ≠ C) :
  -- Complex radicals and a reciprocal whose denominator never vanishes.
  let sqrt := fun z : ℂ => z ^ (2⁻¹ : ℂ)
  let cbrt := fun z : ℂ => z ^ (3⁻¹ : ℂ)
  let inv0 := fun z : ℂ =>
    let e := Real.sign ‖z‖
    (e : ℂ) / (z + ((1 - e : ℝ) : ℂ))
  -- The stationary quartic A*t^4 + B*t^3 + D*t - A.
  let u := X 0 - C 0
  let v := X 1 - C 1
  let A : ℂ := (b * v : ℝ)
  let B : ℂ := (2 * (a ^ 2 + a * u - b ^ 2) : ℝ)
  let D : ℂ := (2 * (b ^ 2 - a ^ 2 + a * u) : ℝ)
  let α := B * inv0 A
  let δ := D * inv0 A
  -- Depress the quartic by t = y - α/4.
  let p := -3 * α ^ 2 / 8
  let q := α ^ 3 / 8 + δ
  let r := -3 * α ^ 4 / 256 - α * δ / 4 - 1
  -- Cardano's root of z^3 + 2*p*z^2 + (p^2 - 4*r)*z - q^2.
  let P := (p ^ 2 - 4 * r) - (2 * p) ^ 2 / 3
  let Q := 2 * (2 * p) ^ 3 / 27 - 2 * p * (p ^ 2 - 4 * r) / 3 - q ^ 2
  let h := sqrt (Q ^ 2 / 4 + P ^ 3 / 27)
  let Uplus := cbrt (-Q / 2 + h)
  let Uminus := cbrt (-Q / 2 - h)
  let U := Uplus + ((1 - Real.sign ‖Uplus‖ : ℝ) : ℂ) * Uminus
  let z := U - P / 3 * inv0 U - 2 * p / 3
  -- Ferrari radicals, with the biquadratic and lower-degree candidates included.
  let s := sqrt z
  let plus := sqrt (-2 * p - z + 2 * q * inv0 s)
  let minus := sqrt (-2 * p - z - 2 * q * inv0 s)
  let w := sqrt (p ^ 2 - 4 * r)
  let biPlus := sqrt ((-p + w) / 2)
  let biMinus := sqrt ((-p - w) / 2)
  let k := sqrt (-D * inv0 B)
  let parameters : List ℝ := [0, k.re, (-k).re,
    ((-s + plus) / 2 - α / 4).re, ((-s - plus) / 2 - α / 4).re,
    ((s + minus) / 2 - α / 4).re, ((s - minus) / 2 - α / 4).re,
    (biPlus - α / 4).re, (-biPlus - α / 4).re,
    (biMinus - α / 4).re, (-biMinus - α / 4).re]
  -- Rational ellipse coordinates, together with the omitted point (-a, 0).
  let point := fun t : ℝ =>
    (a * (1 - t ^ 2) / (1 + t ^ 2), 2 * b * t / (1 + t ^ 2))
  let coefficientsAt := fun xy : ℝ × ℝ =>
    let nx := a ^ 2 * xy.2
    let ny := -b ^ 2 * xy.1
    (nx, ny, nx * (C 0 + xy.1) + ny * (C 1 + xy.2))
  let candidates := ((-a, 0) :: parameters.map point).map coefficientsAt
  -- Keep an incident candidate, or replace it by a valid duplicate.
  let pick := fun (A B D : ℝ) (fallback : ℝ × ℝ × ℝ) =>
    let (A₀, B₀, D₀) := fallback
    let residual := A * X 0 + B * X 1 - D
    let e := 1 - Real.sign (residual ^ 2)
    (e * A + (1 - e) * A₀, e * B + (1 - e) * B₀, e * D + (1 - e) * D₀)
  let fallback := candidates.foldr (fun (A, B, D) acc => pick A B D acc) (0, 0, 0)
  -- Construct the geometric line from its two distinct defining points.
  let normalLine := fun A B : ℝ =>
    let px := C 0 - B / b ^ 2
    let py := C 1 + A / a ^ 2
    line (!₂[px, py] : Point2D) !₂[px - B, py + A]
  let normals := candidates.map fun (A, B, D) =>
    let (A, B, _) := pick A B D fallback
    normalLine A B
  ∀ L : Set Point2D, L ∈ normals ↔
    ∃ Y : Point2D, onEllipse C a b Y ∧
      Y ≠ Y + ellipseNormalDirection C Y a b ∧
      L = line Y (Y + ellipseNormalDirection C Y a b) ∧ X ∈ L := by
  classical
  extract_lets sqrt cbrt inv0 u v A B D α δ p q r P Q h Uplus Uminus U z s
    plus minus w biPlus biMinus k parameters point coefficientsAt candidates pick fallback
    normalLine normals
  have hz : monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2) = z := by rfl
  have hts : ellipseNormalParameters (b * v)
      (2 * (a ^ 2 + a * u - b ^ 2)) (2 * (b ^ 2 - a ^ 2 + a * u)) = parameters := by
    unfold ellipseNormalParameters
    dsimp only
    erw [hz]
    rfl
  have hraw : candidates = ellipseNormalRawLines X C a b := by
    change ((-a, 0) :: parameters.map point).map coefficientsAt = _
    rw [ellipseNormalRawLines_eq_coefficients, ← hts]
  have hne : ∃ L ∈ candidates, lineHolds L.1 L.2.1 L.2.2 X := by
    rw [hraw]
    exact ellipseNormalRawLines_incident X C a b ha.ne' hb.ne' (by tauto)
  let coefficients := candidates.map (fun (A, B, D) => pick A B D fallback)
  have hrepair : coefficients = EllipseNormals.signRepair X candidates := rfl
  have hmem (K : ℝ × ℝ × ℝ) :
      K ∈ coefficients ↔ K ∈ ellipseNormalRawLines X C a b ∧ lineHolds K.1 K.2.1 K.2.2 X := by
    rw [hrepair, EllipseNormals.mem_signRepair_iff X candidates hne K, hraw]
  have hlines : normals = coefficients.map (fun (A, B, _) => normalLine A B) := by
    simp only [normals, coefficients, List.map_map, Function.comp_def]
  have hconstructor (Y : Point2D) :
      (let (A, B, _) := ellipseNormalLine C a b Y
       normalLine A B) = line Y (Y + ellipseNormalDirection C Y a b) :=
    congrArg (fun pq : Point2D × Point2D => line pq.1 pq.2)
      (ellipseNormalLine_constructor_points C Y a b ha.ne' hb.ne')
  intro L
  constructor
  · intro hL
    rw [hlines] at hL
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hL
    obtain ⟨hK, hX⟩ := (hmem K).mp hK
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hK
    have hY := ellipseNormalCandidates_mem X C Y a b hY
    rw [hconstructor]
    refine ⟨Y, hY, ?_, rfl, ?_⟩
    · simpa using ellipseNormalDirection_ne_zero C Y a b ha.ne' hb.ne' hY
    · exact (ellipseNormalThrough_iff_mem_line C X Y a b ha.ne' hb.ne' hY).mp hX
  · rintro ⟨Y, hY, _, rfl, hX⟩
    have hX := (ellipseNormalThrough_iff_mem_line C X Y a b ha.ne' hb.ne' hY).mpr hX
    have hc : Y ∈ ellipseNormalCandidates X C a b :=
      ((ellipseNormalCandidates_iff X C Y a b ha.ne' hb.ne' (by tauto)).mpr ⟨hY, hX⟩).1
    rw [hlines]
    exact List.mem_map.mpr ⟨ellipseNormalLine C a b Y,
      (hmem _).mpr ⟨List.mem_map.mpr ⟨Y, hc, rfl⟩, hX⟩, hconstructor Y⟩

/-- The axis-query example still supplies the two extra normals `y = ±sqrt(5)*(x-1)`. -/
theorem ellipse_axis_additional_normals (s : ℝ) (hs : s ^ 2 = 5) :
    let C : Point2D := !₂[0, 0]
    let X : Point2D := !₂[1, 0]
    let Y : Point2D := !₂[4 / 3, s / 3]
    onEllipse C 2 1 Y ∧ ellipseNormalThrough C 2 1 Y X ∧
      ∀ Z : Point2D, ellipseNormalThrough C 2 1 Y Z ↔ Z 1 = s * (Z 0 - 1) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp only [onEllipse, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sub_zero]
    nlinarith [hs]
  · rw [ellipseNormalLine_holds_iff]
    norm_num
    ring
  · intro Z
    rw [ellipseNormalLine_holds_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
    constructor <;> intro h <;> nlinarith [h]

end
end SympyGeometry
