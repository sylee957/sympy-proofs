module

public import SympyProofs.Geometry.PlaneDistance
public import SympyProofs.Geometry.ConicRadicals
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Point distances to circles, ellipses, parabolas, and hyperbolas

The curves are subsets of Euclidean two-space. Ellipses and hyperbolas have
center `C` and positive axis lengths `a`, `b`; the parabola has vertex `C`
and equation `y - C.y = a * (x - C.x)^2`. Both hyperbola branches are included.
All distances are to the boundary curves, not to filled regions.

The formulas use finite lists of explicit complex radicals and real `min`.
They do not invoke a polynomial root solver. Extra radical candidates are mapped
to actual curve points, and a closest point is proved to occur in each list.
The final functions contain no `if` branches: the parabola compares four points,
and each ellipse/hyperbola compares twelve. Isometric-image theorems also cover
rotated conics by expressing the query point in the conic's coordinate frame.
See `SympyProofs.Geometry.FocusDirectrixParabola` for a focus/directrix constructor
and its distance formula for an arbitrarily oriented directrix.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open scoped Topology

abbrev Point2D := EuclideanSpace ℝ (Fin 2)

def circle (C : Point2D) (r : ℝ) : Set Point2D := Metric.sphere C r

def ellipse (C : Point2D) (a b : ℝ) : Set Point2D :=
  {Y | b ^ 2 * (Y 0 - C 0) ^ 2 + a ^ 2 * (Y 1 - C 1) ^ 2 = a ^ 2 * b ^ 2}

def parabola (C : Point2D) (a : ℝ) : Set Point2D :=
  {Y | Y 1 - C 1 = a * (Y 0 - C 0) ^ 2}

def hyperbola (C : Point2D) (a b : ℝ) : Set Point2D :=
  {Y | b ^ 2 * (Y 0 - C 0) ^ 2 - a ^ 2 * (Y 1 - C 1) ^ 2 = a ^ 2 * b ^ 2}

/-- Explicit squared Euclidean distance. -/
def pointDistanceSq (X Y : Point2D) : ℝ :=
  (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2

theorem dist_sq_pointDistanceSq (X Y : Point2D) : dist X Y ^ 2 = pointDistanceSq X Y := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, Real.dist_eq, pointDistanceSq]

theorem point_distance_coordinates (X Y : Point2D) :
    dist X Y = Real.sqrt (pointDistanceSq X Y) := by
  rw [← dist_sq_pointDistanceSq, Real.sqrt_sq dist_nonneg]

/-- A finite expression made only of squared coordinate distances and `min`. -/
def conicMinimumSq (X base : Point2D) (candidates : List Point2D) : ℝ :=
  candidates.foldr (fun Y m => min (pointDistanceSq X Y) m) (pointDistanceSq X base)

private theorem le_conicMinimumSq (X base : Point2D) (ys : List Point2D) (m : ℝ)
    (hb : m ≤ pointDistanceSq X base) (hy : ∀ Y ∈ ys, m ≤ pointDistanceSq X Y) :
    m ≤ conicMinimumSq X base ys := by
  induction ys with
  | nil => exact hb
  | cons y ys ih =>
    exact le_min (hy y (by simp)) (ih (fun Y hY => hy Y (by simp [hY])))

private theorem conicMinimumSq_le_base (X base : Point2D) (ys : List Point2D) :
    conicMinimumSq X base ys ≤ pointDistanceSq X base := by
  induction ys with
  | nil => exact le_rfl
  | cons y ys ih => exact (min_le_right _ _).trans ih

private theorem conicMinimumSq_le_mem (X base Y : Point2D) (ys : List Point2D) (hY : Y ∈ ys) :
    conicMinimumSq X base ys ≤ pointDistanceSq X Y := by
  induction ys with
  | nil => simp at hY
  | cons y ys ih =>
    rcases List.mem_cons.mp hY with rfl | hY
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hY)

private theorem infDist_eq_radical_minimum (S : Set Point2D) (X base : Point2D)
    (ys : List Point2D) (hb : base ∈ S) (hys : ∀ Y ∈ ys, Y ∈ S)
    (hattain : ∃ Y ∈ S, Metric.infDist X S = dist X Y ∧ (Y = base ∨ Y ∈ ys)) :
    Metric.infDist X S = Real.sqrt (conicMinimumSq X base ys) := by
  obtain ⟨Y, hY, he, hc⟩ := hattain
  have hle (Z : Point2D) (hZ : Z ∈ S) : pointDistanceSq X Y ≤ pointDistanceSq X Z := by
    rw [← dist_sq_pointDistanceSq, ← dist_sq_pointDistanceSq]
    exact pow_le_pow_left₀ dist_nonneg (he ▸ Metric.infDist_le_dist_of_mem hZ) 2
  have hmin : conicMinimumSq X base ys = pointDistanceSq X Y := by
    apply le_antisymm
    · rcases hc with rfl | hc
      · exact conicMinimumSq_le_base _ _ _
      · exact conicMinimumSq_le_mem _ _ _ _ hc
    · exact le_conicMinimumSq _ _ _ _ (hle base hb) (fun Z hZ => hle Z (hys Z hZ))
  rw [hmin, ← point_distance_coordinates, he]

theorem distance_singleton_of_isClosed (S : Set Point2D) (hS : IsClosed S)
    (hne : S.Nonempty) (X : Point2D) : distance {X} S = Metric.infDist X S := by
  obtain ⟨Y, hY, he⟩ := hS.exists_infDist_eq_dist hne X
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨X, by simp, Y, hY, he.symm⟩
  · rintro r ⟨Z, hZ, Y, hY, rfl⟩
    simpa only [Set.mem_singleton_iff.mp hZ] using Metric.infDist_le_dist_of_mem hY

def pointCircleDistance (X C : Point2D) (r : ℝ) : ℝ :=
  |Real.sqrt (pointDistanceSq X C) - r|

/-- Circle distance, also including radius zero. -/
theorem point_circle_distance (X C : Point2D) (r : ℝ) (hr : 0 ≤ r) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    Metric.infDist X (circle C r) = |Real.sqrt (u ^ 2 + v ^ 2) - r| := by
  change Metric.infDist X (circle C r) = pointCircleDistance X C r
  unfold pointCircleDistance
  rw [← point_distance_coordinates]
  have hlower (Y : Point2D) (hY : Y ∈ circle C r) : |dist X C - r| ≤ dist X Y := by
    simpa only [show dist Y C = r from hY] using abs_dist_sub_le X Y C
  have hattain : ∃ Y ∈ circle C r, dist X Y = |dist X C - r| := by
    by_cases hXC : X = C
    · subst X
      refine ⟨C + !₂[r, 0], ?_, ?_⟩
      · change dist (C + !₂[r, 0]) C = r
        rw [dist_eq_norm, add_sub_cancel_left]
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.sqrt_sq hr]
      · rw [dist_self, zero_sub, abs_neg, abs_of_nonneg hr, dist_comm,
          dist_eq_norm, add_sub_cancel_left]
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.sqrt_sq hr]
    · have hn : ‖X - C‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hXC)
      refine ⟨C + (r / ‖X - C‖) • (X - C), ?_, ?_⟩
      · change dist (C + (r / ‖X - C‖) • (X - C)) C = r
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr (norm_nonneg _)), div_mul_cancel₀ _ hn]
      · have he : X - (C + (r / ‖X - C‖) • (X - C)) =
            (1 - r / ‖X - C‖) • (X - C) := by rw [sub_smul, one_smul]; abel
        rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, dist_eq_norm,
          ← abs_of_nonneg (norm_nonneg (X - C)), ← abs_mul]
        congr 1
        field_simp
        simp only [abs_norm]
        ring
  obtain ⟨Y, hY, he⟩ := hattain
  exact le_antisymm ((Metric.infDist_le_dist_of_mem hY).trans_eq he)
    ((Metric.le_infDist ⟨Y, hY⟩).mpr hlower)

def parabolaPoint (C : Point2D) (a t : ℝ) : Point2D := C + !₂[t, a * t ^ 2]

@[simp] theorem parabolaPoint_mem (C : Point2D) (a t : ℝ) :
    parabolaPoint C a t ∈ parabola C a := by simp [parabolaPoint, parabola]

theorem parabola_isClosed (C : Point2D) (a : ℝ) : IsClosed (parabola C a) := by
  apply isClosed_eq <;> fun_prop

theorem mem_parabola_iff (C Y : Point2D) (a : ℝ) :
    Y ∈ parabola C a ↔ ∃ t, parabolaPoint C a t = Y := by
  constructor
  · intro h
    refine ⟨Y 0 - C 0, ?_⟩
    ext i
    fin_cases i <;> simp [parabolaPoint]
    change Y 1 - C 1 = a * (Y 0 - C 0) ^ 2 at h
    linarith
  · rintro ⟨t, rfl⟩; exact parabolaPoint_mem _ _ _

theorem parabola_dist_sq (X C : Point2D) (a t : ℝ) :
    dist X (parabolaPoint C a t) ^ 2 =
      (t - (X 0 - C 0)) ^ 2 + (a * t ^ 2 - (X 1 - C 1)) ^ 2 := by
  rw [dist_sq_pointDistanceSq]
  simp [pointDistanceSq, parabolaPoint]
  ring

private theorem parabola_stationary (X C : Point2D) (a t : ℝ)
    (hmin : ∀ s, dist X (parabolaPoint C a t) ≤ dist X (parabolaPoint C a s)) :
    2 * a ^ 2 * t ^ 3 + (1 - 2 * a * (X 1 - C 1)) * t - (X 0 - C 0) = 0 := by
  let u := X 0 - C 0
  let v := X 1 - C 1
  have hm : IsLocalMin (fun s : ℝ => (s - u) ^ 2 + (a * s ^ 2 - v) ^ 2) t := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [parabola_dist_sq] using pow_le_pow_left₀ dist_nonneg (hmin s) 2
  have hd := (((hasDerivAt_id t).sub_const u).pow 2).add
    (((((hasDerivAt_id t).pow 2).const_mul a).sub_const v).pow 2)
  have he := hm.hasDerivAt_eq_zero hd
  dsimp at he
  change 2 * a ^ 2 * t ^ 3 + (1 - 2 * a * v) * t - u = 0
  linear_combination he / 2

def parabolaCandidates (X C : Point2D) (a : ℝ) : List Point2D :=
  let u := X 0 - C 0
  let v := X 1 - C 1
  (cubicRadicals ((1 - 2 * a * v) / (2 * a ^ 2) : ℝ)
    (-u / (2 * a ^ 2) : ℝ)).map (fun z => parabolaPoint C a z.re)

def pointParabolaDistance (X C : Point2D) (a : ℝ) : ℝ :=
  Real.sqrt (conicMinimumSq X (parabolaPoint C a 0) (parabolaCandidates X C a))

private theorem point_parabola_distance_eq (X C : Point2D) (a : ℝ) (ha : a ≠ 0) :
    Metric.infDist X (parabola C a) = pointParabolaDistance X C a := by
  apply infDist_eq_radical_minimum _ _ _ _ (parabolaPoint_mem _ _ _)
  · intro Y hY
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hY
    exact parabolaPoint_mem _ _ _
  · obtain ⟨Y, hY, he⟩ := (parabola_isClosed C a).exists_infDist_eq_dist
      ⟨_, parabolaPoint_mem C a 0⟩ X
    obtain ⟨t, rfl⟩ := (mem_parabola_iff C Y a).mp hY
    have ht := parabola_stationary X C a t (fun s =>
      he ▸ Metric.infDist_le_dist_of_mem (parabolaPoint_mem C a s))
    have hn : 2 * a ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)
    have hroot : t ^ 3 + (1 - 2 * a * (X 1 - C 1)) / (2 * a ^ 2) * t +
        (-(X 0 - C 0)) / (2 * a ^ 2) = 0 := by
      field_simp
      linear_combination ht
    refine ⟨_, parabolaPoint_mem _ _ _, he, Or.inr ?_⟩
    apply List.mem_map.mpr
    refine ⟨(t : ℂ), mem_cubicRadicals _ _ _ ?_, by simp⟩
    exact_mod_cast hroot

private theorem pointParabolaDistance_eq_coordinates (X C : Point2D) (a : ℝ) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    let f := fun t : ℝ => (t - u) ^ 2 + (a * t ^ 2 - v) ^ 2
    pointParabolaDistance X C a = Real.sqrt
      ((cubicRadicals ((1 - 2 * a * v) / (2 * a ^ 2) : ℝ) (-u / (2 * a ^ 2) : ℝ)).foldr
        (fun z m => min (f z.re) m) (u ^ 2 + v ^ 2)) := by
  have hdist (t : ℝ) : pointDistanceSq X (parabolaPoint C a t) =
      (t - (X 0 - C 0)) ^ 2 + (a * t ^ 2 - (X 1 - C 1)) ^ 2 := by
    rw [← dist_sq_pointDistanceSq, parabola_dist_sq]
  simp only [pointParabolaDistance, conicMinimumSq, parabolaCandidates,
    List.foldr_map, hdist, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_sub, neg_sq]

/-- Point-to-parabola distance with Cardano's radicals and the finite minimum written out.
The complex square and cube roots are `sqrtC` and `cbrtC`. -/
theorem point_parabola_distance (X C : Point2D) (a : ℝ) (ha : a ≠ 0) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    let inv := fun z : ℂ => (Real.sign ‖z‖ : ℂ) / (z + ((1 - Real.sign ‖z‖ : ℝ) : ℂ))
    let p : ℂ := ((1 - 2 * a * v) / (2 * a ^ 2) : ℝ)
    let q : ℂ := (-u / (2 * a ^ 2) : ℝ)
    let d := sqrtC (q ^ 2 / 4 + p ^ 3 / 27)
    let c₁ := cbrtC (-q / 2 + d)
    let c₂ := cbrtC (-q / 2 - d)
    let c := c₁ + ((1 - Real.sign ‖c₁‖ : ℝ) : ℂ) * c₂
    let z := c - p / 3 * inv c
    let s := sqrtC (-3 * z ^ 2 - 4 * p)
    let f := fun t : ℝ => (t - u) ^ 2 + (a * t ^ 2 - v) ^ 2
    Metric.infDist X (parabola C a) = Real.sqrt
      (min (f z.re) (min (f ((-z + s) / 2).re)
        (min (f ((-z - s) / 2).re) (u ^ 2 + v ^ 2)))) := by
  rw [point_parabola_distance_eq X C a ha]
  simpa only [cubicRadicals, depressedCubicRoot, cardanoU, radicalInv, radicalDenom,
    List.foldr_cons, List.foldr_nil] using pointParabolaDistance_eq_coordinates X C a

/-- Unified signed-axis conic: `k = 1` is an ellipse, `k = -1` a hyperbola. -/
def axisConic (C : Point2D) (a b k : ℝ) : Set Point2D :=
  {Y | b ^ 2 * (Y 0 - C 0) ^ 2 + k * a ^ 2 * (Y 1 - C 1) ^ 2 = a ^ 2 * b ^ 2}

def conicPole (C : Point2D) (a : ℝ) : Point2D := C + !₂[-a, 0]

def conicPoint (C : Point2D) (a b k t : ℝ) : Point2D :=
  C + !₂[a * (1 - k * t ^ 2) / (1 + k * t ^ 2), 2 * b * t / (1 + k * t ^ 2)]

theorem axisConic_isClosed (C : Point2D) (a b k : ℝ) : IsClosed (axisConic C a b k) := by
  apply isClosed_eq <;> fun_prop

@[simp] theorem conicPole_mem (C : Point2D) (a b k : ℝ) :
    conicPole C a ∈ axisConic C a b k := by simp [axisConic, conicPole]; ring

theorem conicPoint_mem (C : Point2D) (a b k t : ℝ) (hk : k = 1 ∨ k = -1)
    (ht : 1 + k * t ^ 2 ≠ 0) : conicPoint C a b k t ∈ axisConic C a b k := by
  simp only [axisConic, Set.mem_ofPred, conicPoint, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, add_sub_cancel_left]
  field_simp
  rcases hk with rfl | rfl <;> ring

/-- Move the two excluded hyperbola parameters to zero; all other parameters are unchanged. -/
def conicSafeParam (k t : ℝ) : ℝ := t * Real.sign |1 + k * t ^ 2|

theorem conicSafeParam_eq (k t : ℝ) (h : 1 + k * t ^ 2 ≠ 0) : conicSafeParam k t = t := by
  simp [conicSafeParam, Real.sign_of_pos (abs_pos.mpr h)]

theorem conicSafeParam_valid (k t : ℝ) : 1 + k * conicSafeParam k t ^ 2 ≠ 0 := by
  by_cases h : 1 + k * t ^ 2 = 0
  · simp [conicSafeParam, h]
  · rwa [conicSafeParam_eq k t h]

def conicSafePoint (C : Point2D) (a b k t : ℝ) : Point2D :=
  conicPoint C a b k (conicSafeParam k t)

theorem conicSafePoint_mem (C : Point2D) (a b k t : ℝ) (hk : k = 1 ∨ k = -1) :
    conicSafePoint C a b k t ∈ axisConic C a b k :=
  conicPoint_mem C a b k _ hk (conicSafeParam_valid k t)

theorem axisConic_parametrization (C Y : Point2D) (a b k : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : k = 1 ∨ k = -1)
    (hY : Y ∈ axisConic C a b k) :
    Y = conicPole C a ∨ ∃ t, 1 + k * t ^ 2 ≠ 0 ∧ conicPoint C a b k t = Y := by
  let x := Y 0 - C 0
  let y := Y 1 - C 1
  change b ^ 2 * x ^ 2 + k * a ^ 2 * y ^ 2 = a ^ 2 * b ^ 2 at hY
  by_cases hx : x + a = 0
  · left
    have hx' : x = -a := by linarith
    have hy' : a ^ 2 * y ^ 2 = 0 := by
      rcases hk with rfl | rfl <;> rw [hx'] at hY <;> nlinarith [hY]
    have hy : y = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
      ((mul_eq_zero.mp hy').resolve_left (pow_ne_zero 2 ha))
    ext i
    fin_cases i
    · change Y 0 = C 0 + -a; dsimp [x] at hx'; linarith
    · change Y 1 = C 1 + 0; dsimp [y] at hy; linarith
  · right
    let t := a * y / (b * (x + a))
    have hd : 1 + k * t ^ 2 = 2 * a / (x + a) := by
      dsimp [t]
      field_simp
      linear_combination hY
    have ht : 1 + k * t ^ 2 ≠ 0 := by
      rw [hd]
      exact div_ne_zero (mul_ne_zero (by norm_num) ha) hx
    refine ⟨t, ht, ?_⟩
    have hpx : a * (1 - k * t ^ 2) / (1 + k * t ^ 2) = x := by
      rw [show 1 - k * t ^ 2 = 2 - (1 + k * t ^ 2) by ring, hd]
      field_simp
      ring
    have hpy : 2 * b * t / (1 + k * t ^ 2) = y := by
      rw [hd]
      dsimp [t]
      field_simp
    ext i
    fin_cases i
    · change C 0 + a * (1 - k * t ^ 2) / (1 + k * t ^ 2) = Y 0
      rw [hpx]; dsimp [x]; ring
    · change C 1 + 2 * b * t / (1 + k * t ^ 2) = Y 1
      rw [hpy]; dsimp [y]; ring

def conicResidualSq (a b k u v t : ℝ) : ℝ :=
  (a * (1 - k * t ^ 2) / (1 + k * t ^ 2) - u) ^ 2 +
    (2 * b * t / (1 + k * t ^ 2) - v) ^ 2

theorem conic_dist_sq (X C : Point2D) (a b k t : ℝ) :
    dist X (conicPoint C a b k t) ^ 2 =
      conicResidualSq a b k (X 0 - C 0) (X 1 - C 1) t := by
  rw [dist_sq_pointDistanceSq]
  simp only [pointDistanceSq, conicPoint, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, conicResidualSq]
  ring

/-- The stationary numerator is a sparse quartic. -/
def conicStationary (a b k u v t : ℝ) : ℝ :=
  b * v * t ^ 4 + 2 * (a ^ 2 + a * u - k * b ^ 2) * t ^ 3 +
    2 * (b ^ 2 - k * a ^ 2 + k * a * u) * t - b * v

theorem hasDerivAt_conicResidualSq (a b k u v t : ℝ) (hk : k = 1 ∨ k = -1)
    (ht : 1 + k * t ^ 2 ≠ 0) :
    HasDerivAt (conicResidualSq a b k u v)
      (4 * conicStationary a b k u v t / (1 + k * t ^ 2) ^ 3) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).add (((hasDerivAt_id t).pow 2).const_mul k)
  have hx := ((hasDerivAt_const t (1 : ℝ)).sub (((hasDerivAt_id t).pow 2).const_mul k)).const_mul a
  have hy := (hasDerivAt_id t).const_mul (2 * b)
  convert (((hx.div hd ht).sub_const u).pow 2).add
    (((hy.div hd ht).sub_const v).pow 2) using 1
  · ext s; rfl
  · dsimp [conicStationary]
    simp only [pow_one, mul_one, zero_add, zero_sub]
    apply (div_eq_iff (pow_ne_zero 3 ht)).mpr
    rcases hk with rfl | rfl <;>
      simp only [one_mul, neg_one_mul] at ht ⊢ <;>
      field_simp [ht] <;> ring

private theorem conic_stationary_of_min (X C : Point2D) (a b k t : ℝ)
    (hk : k = 1 ∨ k = -1) (ht : 1 + k * t ^ 2 ≠ 0)
    (hmin : ∀ Y ∈ axisConic C a b k, dist X (conicPoint C a b k t) ≤ dist X Y) :
    conicStationary a b k (X 0 - C 0) (X 1 - C 1) t = 0 := by
  have hc : Continuous (fun s : ℝ => 1 + k * s ^ 2) := by fun_prop
  have hne : ∀ᶠ s in 𝓝 t, 1 + k * s ^ 2 ≠ 0 := hc.continuousAt.eventually_ne ht
  have hm : IsLocalMin (conicResidualSq a b k (X 0 - C 0) (X 1 - C 1)) t := by
    filter_upwards [hne] with s hs
    simpa only [conic_dist_sq] using pow_le_pow_left₀ dist_nonneg
      (hmin _ (conicPoint_mem C a b k s hk hs)) 2
  have he := hm.hasDerivAt_eq_zero
    (hasDerivAt_conicResidualSq a b k (X 0 - C 0) (X 1 - C 1) t hk ht)
  exact (mul_eq_zero.mp ((div_eq_zero_iff).mp he |>.resolve_right
    (pow_ne_zero 3 ht))).resolve_left (by norm_num)

def axisConicCandidates (X C : Point2D) (a b k : ℝ) : List Point2D :=
  let u := X 0 - C 0
  let v := X 1 - C 1
  (sparseQuarticRadicals (b * v) (2 * (a ^ 2 + a * u - k * b ^ 2))
    (2 * (b ^ 2 - k * a ^ 2 + k * a * u))).map (conicSafePoint C a b k)

def axisConicDistance (X C : Point2D) (a b k : ℝ) : ℝ :=
  Real.sqrt (conicMinimumSq X (conicPole C a) (axisConicCandidates X C a b k))

/-- An identically zero stationary polynomial is precisely the centered circle case
under the conic hypotheses; its pole is already a closest point. -/
private theorem conic_zero_stationary_distance (X C Y : Point2D) (a b k : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : k = 1 ∨ k = -1)
    (hY : Y ∈ axisConic C a b k)
    (hA : b * (X 1 - C 1) = 0)
    (hB : 2 * (a ^ 2 + a * (X 0 - C 0) - k * b ^ 2) = 0)
    (hD : 2 * (b ^ 2 - k * a ^ 2 + k * a * (X 0 - C 0)) = 0) :
    dist X Y = dist X (conicPole C a) := by
  have hv : X 1 - C 1 = 0 := (mul_eq_zero.mp hA).resolve_left hb
  rcases hk with rfl | rfl
  · have hu : a * (X 0 - C 0) = 0 := by linarith
    have hu' : X 0 - C 0 = 0 := (mul_eq_zero.mp hu).resolve_left ha
    have hXC : X = C := by
      ext i; fin_cases i
      · exact sub_eq_zero.mp hu'
      · exact sub_eq_zero.mp hv
    subst X
    have hab : a ^ 2 = b ^ 2 := by simp only [sub_self, mul_zero, one_mul] at hB; linarith
    change b ^ 2 * (Y 0 - C 0) ^ 2 + 1 * a ^ 2 * (Y 1 - C 1) ^ 2 =
      a ^ 2 * b ^ 2 at hY
    have hf : a ^ 2 * ((Y 0 - C 0) ^ 2 + (Y 1 - C 1) ^ 2 - a ^ 2) = 0 := by
      linear_combination hY + ((Y 0 - C 0) ^ 2 - a ^ 2) * hab
    have hh := (mul_eq_zero.mp hf).resolve_left (pow_ne_zero 2 ha)
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_sq_pointDistanceSq, pointDistanceSq, conicPole, PiLp.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [hh]
  · exfalso
    have : a ^ 2 + b ^ 2 = 0 := by nlinarith [hB, hD]
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]

theorem point_axisConic_distance (X C : Point2D) (a b k : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk : k = 1 ∨ k = -1) :
    Metric.infDist X (axisConic C a b k) = axisConicDistance X C a b k := by
  apply infDist_eq_radical_minimum _ _ _ _ (conicPole_mem _ _ _ _)
  · intro Y hY
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hY
    exact conicSafePoint_mem C a b k t hk
  · obtain ⟨Y, hY, he⟩ := (axisConic_isClosed C a b k).exists_infDist_eq_dist
      ⟨_, conicPole_mem C a b k⟩ X
    by_cases hz : b * (X 1 - C 1) = 0 ∧
        2 * (a ^ 2 + a * (X 0 - C 0) - k * b ^ 2) = 0 ∧
        2 * (b ^ 2 - k * a ^ 2 + k * a * (X 0 - C 0)) = 0
    · refine ⟨conicPole C a, conicPole_mem _ _ _ _, ?_, Or.inl rfl⟩
      exact he.trans (conic_zero_stationary_distance X C Y a b k ha hb hk hY hz.1 hz.2.1 hz.2.2)
    · have hn : b * (X 1 - C 1) ≠ 0 ∨
          2 * (a ^ 2 + a * (X 0 - C 0) - k * b ^ 2) ≠ 0 ∨
          2 * (b ^ 2 - k * a ^ 2 + k * a * (X 0 - C 0)) ≠ 0 := by tauto
      rcases axisConic_parametrization C Y a b k ha hb hk hY with hp | ⟨t, ht, rfl⟩
      · exact ⟨Y, hY, he, Or.inl hp⟩
      · have hstat := conic_stationary_of_min X C a b k t hk ht
          (fun Z hZ => he ▸ Metric.infDist_le_dist_of_mem hZ)
        refine ⟨_, hY, he, Or.inr ?_⟩
        apply List.mem_map.mpr
        exact ⟨t, mem_sparseQuarticRadicals _ _ _ _ hn hstat,
          by simp only [conicSafePoint, conicSafeParam_eq k t ht]⟩

def pointEllipseDistance (X C : Point2D) (a b : ℝ) : ℝ := axisConicDistance X C a b 1

def pointHyperbolaDistance (X C : Point2D) (a b : ℝ) : ℝ := axisConicDistance X C a b (-1)

private theorem axisConicDistance_eq_coordinates (X C : Point2D) (a b k : ℝ) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    let A := b * v
    let B := 2 * (a ^ 2 + a * u - k * b ^ 2)
    let D := 2 * (b ^ 2 - k * a ^ 2 + k * a * u)
    let f := fun t : ℝ =>
      (a * (1 - k * t ^ 2) / (1 + k * t ^ 2) - u) ^ 2 +
        (2 * b * t / (1 + k * t ^ 2) - v) ^ 2
    axisConicDistance X C a b k = Real.sqrt
      ((sparseQuarticRadicals A B D).foldr
        (fun t m => min (f (t * Real.sign |1 + k * t ^ 2|)) m) ((u + a) ^ 2 + v ^ 2)) := by
  have hdist (t : ℝ) : pointDistanceSq X (conicSafePoint C a b k t) =
      conicResidualSq a b k (X 0 - C 0) (X 1 - C 1) (conicSafeParam k t) := by
    rw [← dist_sq_pointDistanceSq, conicSafePoint, conic_dist_sq]
  have hpole : pointDistanceSq X (conicPole C a) =
      (X 0 - C 0 + a) ^ 2 + (X 1 - C 1) ^ 2 := by
    simp only [pointDistanceSq, conicPole, PiLp.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  simp only [axisConicDistance, conicMinimumSq, axisConicCandidates,
    List.foldr_map, hdist, hpole, conicResidualSq, conicSafeParam]

private theorem point_ellipse_distance_eq (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Metric.infDist X (ellipse C a b) = pointEllipseDistance X C a b := by
  simpa only [axisConic, one_mul, ellipse, pointEllipseDistance] using
    point_axisConic_distance X C a b 1 ha.ne' hb.ne' (Or.inl rfl)

private theorem point_hyperbola_distance_eq (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Metric.infDist X (hyperbola C a b) = pointHyperbolaDistance X C a b := by
  simpa only [axisConic, neg_one_mul, neg_mul, one_mul, ← sub_eq_add_neg, hyperbola,
    pointHyperbolaDistance] using
    point_axisConic_distance X C a b (-1) ha.ne' hb.ne' (Or.inr rfl)

/-- Ellipse distance with Ferrari's radicals written out using local scalar definitions.
The extra candidates cover repeated roots, circles, and points on either axis. -/
theorem point_ellipse_distance (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    let inv := fun z : ℂ => (Real.sign ‖z‖ : ℂ) / (z + ((1 - Real.sign ‖z‖ : ℝ) : ℂ))
    let A : ℝ := b * v
    let B : ℝ := 2 * (a ^ 2 + a * u - b ^ 2)
    let D : ℝ := 2 * (b ^ 2 - a ^ 2 + a * u)
    let β := (B : ℂ) * inv A
    let δ := (D : ℂ) * inv A
    let p := -(3 * β ^ 2 / 8)
    let q := β ^ 3 / 8 + δ
    let r := -3 * β ^ 4 / 256 - β * δ / 4 - 1
    let P := (p ^ 2 - 4 * r) - (2 * p) ^ 2 / 3
    let Q := 2 * (2 * p) ^ 3 / 27 - (2 * p) * (p ^ 2 - 4 * r) / 3 - q ^ 2
    let d := sqrtC (Q ^ 2 / 4 + P ^ 3 / 27)
    let c₁ := cbrtC (-Q / 2 + d)
    let c₂ := cbrtC (-Q / 2 - d)
    let c := c₁ + ((1 - Real.sign ‖c₁‖ : ℝ) : ℂ) * c₂
    let z := c - P / 3 * inv c - (2 * p) / 3
    let s := sqrtC z
    let s₁ := sqrtC (-2 * p - z + 2 * q * inv s)
    let s₂ := sqrtC (-2 * p - z - 2 * q * inv s)
    let w := sqrtC (p ^ 2 - 4 * r)
    let w₁ := sqrtC ((-p + w) / 2)
    let w₂ := sqrtC ((-p - w) / 2)
    let h := sqrtC (-(D : ℂ) * inv B)
    let ts := [0, h.re, (-h).re] ++
      ([(-s + s₁) / 2, (-s - s₁) / 2, (s + s₂) / 2, (s - s₂) / 2,
        w₁, -w₁, w₂, -w₂].map (fun z => (z - β / 4).re))
    let f := fun t : ℝ =>
      (a * (1 - t ^ 2) / (1 + t ^ 2) - u) ^ 2 + (2 * b * t / (1 + t ^ 2) - v) ^ 2
    Metric.infDist X (ellipse C a b) =
      Real.sqrt (ts.foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2)) := by
  intro u v inv A B D β δ p q r P Q d c₁ c₂ c z s s₁ s₂ w w₁ w₂ h ts f
  rw [point_ellipse_distance_eq X C a b ha hb]
  have hz : monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2) = z := by
    unfold monicCubicRoot
    rw [← sub_eq_add_neg]
    rfl
  have hts : sparseQuarticRadicals A B D = ts := by
    change [0, h.re, (-h).re] ++
      ((depressedQuarticRadicals (0 - 3 * β ^ 2 / 8) (β ^ 3 / 8 - β * 0 / 2 + δ)
        (-3 * β ^ 4 / 256 + β ^ 2 * 0 / 16 - β * δ / 4 + -1)).map
          (fun z => z - β / 4)).map Complex.re = ts
    simp only [mul_zero, zero_div, sub_zero, add_zero, zero_sub, ← sub_eq_add_neg]
    change [0, h.re, (-h).re] ++
      ((depressedQuarticRadicals p q r).map (fun z => z - β / 4)).map Complex.re = ts
    unfold depressedQuarticRadicals
    rw [hz]
    rfl
  have hs (t : ℝ) : Real.sign |1 + t ^ 2| = 1 :=
    Real.sign_of_pos (abs_pos.mpr (ne_of_gt (by positivity)))
  have he := axisConicDistance_eq_coordinates X C a b 1
  simp only [one_mul, hs, mul_one] at he
  change pointEllipseDistance X C a b = Real.sqrt
    ((sparseQuarticRadicals A B D).foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2)) at he
  exact he.trans (congrArg (fun ts => Real.sqrt
    (ts.foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2))) hts)

/-- Distance to both hyperbola branches with Ferrari's radicals written out.
The `sign` factor moves excluded parameters to zero without a conditional branch. -/
theorem point_hyperbola_distance (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let u := X 0 - C 0
    let v := X 1 - C 1
    let inv := fun z : ℂ => (Real.sign ‖z‖ : ℂ) / (z + ((1 - Real.sign ‖z‖ : ℝ) : ℂ))
    let A : ℝ := b * v
    let B : ℝ := 2 * (a ^ 2 + a * u + b ^ 2)
    let D : ℝ := 2 * (b ^ 2 + a ^ 2 - a * u)
    let β := (B : ℂ) * inv A
    let δ := (D : ℂ) * inv A
    let p := -(3 * β ^ 2 / 8)
    let q := β ^ 3 / 8 + δ
    let r := -3 * β ^ 4 / 256 - β * δ / 4 - 1
    let P := (p ^ 2 - 4 * r) - (2 * p) ^ 2 / 3
    let Q := 2 * (2 * p) ^ 3 / 27 - (2 * p) * (p ^ 2 - 4 * r) / 3 - q ^ 2
    let d := sqrtC (Q ^ 2 / 4 + P ^ 3 / 27)
    let c₁ := cbrtC (-Q / 2 + d)
    let c₂ := cbrtC (-Q / 2 - d)
    let c := c₁ + ((1 - Real.sign ‖c₁‖ : ℝ) : ℂ) * c₂
    let z := c - P / 3 * inv c - (2 * p) / 3
    let s := sqrtC z
    let s₁ := sqrtC (-2 * p - z + 2 * q * inv s)
    let s₂ := sqrtC (-2 * p - z - 2 * q * inv s)
    let w := sqrtC (p ^ 2 - 4 * r)
    let w₁ := sqrtC ((-p + w) / 2)
    let w₂ := sqrtC ((-p - w) / 2)
    let h := sqrtC (-(D : ℂ) * inv B)
    let ts := [0, h.re, (-h).re] ++
      ([(-s + s₁) / 2, (-s - s₁) / 2, (s + s₂) / 2, (s - s₂) / 2,
        w₁, -w₁, w₂, -w₂].map (fun z => (z - β / 4).re))
    let f := fun t : ℝ =>
      let t := t * Real.sign |1 - t ^ 2|
      (a * (1 + t ^ 2) / (1 - t ^ 2) - u) ^ 2 + (2 * b * t / (1 - t ^ 2) - v) ^ 2
    Metric.infDist X (hyperbola C a b) =
      Real.sqrt (ts.foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2)) := by
  intro u v inv A B D β δ p q r P Q d c₁ c₂ c z s s₁ s₂ w w₁ w₂ h ts f
  rw [point_hyperbola_distance_eq X C a b ha hb]
  have hz : monicCubicRoot (2 * p) (p ^ 2 - 4 * r) (-q ^ 2) = z := by
    unfold monicCubicRoot
    rw [← sub_eq_add_neg]
    rfl
  have hts : sparseQuarticRadicals A B D = ts := by
    change [0, h.re, (-h).re] ++
      ((depressedQuarticRadicals (0 - 3 * β ^ 2 / 8) (β ^ 3 / 8 - β * 0 / 2 + δ)
        (-3 * β ^ 4 / 256 + β ^ 2 * 0 / 16 - β * δ / 4 + -1)).map
          (fun z => z - β / 4)).map Complex.re = ts
    simp only [mul_zero, zero_div, sub_zero, add_zero, zero_sub, ← sub_eq_add_neg]
    change [0, h.re, (-h).re] ++
      ((depressedQuarticRadicals p q r).map (fun z => z - β / 4)).map Complex.re = ts
    unfold depressedQuarticRadicals
    rw [hz]
    rfl
  have he := axisConicDistance_eq_coordinates X C a b (-1)
  simp only [neg_mul, one_mul, sub_neg_eq_add, ← sub_eq_add_neg] at he
  change pointHyperbolaDistance X C a b = Real.sqrt
    ((sparseQuarticRadicals A B D).foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2)) at he
  exact he.trans (congrArg (fun ts => Real.sqrt
    (ts.foldr (fun t m => min (f t) m) ((u + a) ^ 2 + v ^ 2))) hts)

/-- Moving a conic by a Euclidean isometry amounts to transforming the query point back. -/
theorem infDist_isometric_image (e : Point2D ≃ᵢ Point2D) (X : Point2D) (S : Set Point2D) :
    Metric.infDist X (e '' S) = Metric.infDist (e.symm X) S := by
  simpa only [e.apply_symm_apply] using Metric.infDist_image (x := e.symm X) (t := S) e.isometry

theorem point_ellipse_distance_isometric (e : Point2D ≃ᵢ Point2D)
    (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Metric.infDist X (e '' ellipse C a b) = pointEllipseDistance (e.symm X) C a b := by
  rw [infDist_isometric_image, point_ellipse_distance_eq _ _ _ _ ha hb]

theorem point_parabola_distance_isometric (e : Point2D ≃ᵢ Point2D)
    (X C : Point2D) (a : ℝ) (ha : a ≠ 0) :
    Metric.infDist X (e '' parabola C a) = pointParabolaDistance (e.symm X) C a := by
  rw [infDist_isometric_image, point_parabola_distance_eq _ _ _ ha]

theorem point_hyperbola_distance_isometric (e : Point2D ≃ᵢ Point2D)
    (X C : Point2D) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Metric.infDist X (e '' hyperbola C a b) = pointHyperbolaDistance (e.symm X) C a b := by
  rw [infDist_isometric_image, point_hyperbola_distance_eq _ _ _ _ ha hb]

end
end SympyGeometry
