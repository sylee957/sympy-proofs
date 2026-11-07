module

public import SympyProofs.Geometry.PolygonPolygonDistance
public import SympyProofs.Geometry.PolygonWinding
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Connected.Clopen

/-!
# Distance between filled polygonal regions

The boundary-distance formula also computes the distance between disjoint
filled regions. Intersecting filled regions have distance zero, including
strict containment with disjoint boundaries.

`filledPolygonDistance` multiplies the boundary distance by the two outside
indicators obtained by querying one vertex of each polygon against the other.
`filled_polygon_isLeast` proves that the result is the attained minimum over
all points of the two `Polygon.filledRegion` sets. There are no simplicity,
convexity, orientation, or nondegeneracy assumptions. The vertex counts must
be positive. Filling uses odd crossing parity and includes the entire path,
even for retraced edges or a twice-traversed loop.

`windingPolygonDistance` expresses the same result using the parity of the
angular winding number. Its correctness theorem minimizes over
`Polygon.windingFilledRegion`, which is characterized by odd winding.
-/

@[expose] public section

namespace SympyGeometry

noncomputable section

open Classical

namespace Polygon

/-- A closed region represented by a polygonal path. The path is contained
in the region and contains its topological frontier. The inclusions allow
degenerate edges and paths traversing parts of the region's interior. -/
structure BoundsRegion {n : ℕ} (p : Polygon Point2D n) (region : Set Point2D) : Prop where
  isClosed : IsClosed region
  boundary_subset : p.boundary ℝ ⊆ region
  frontier_subset : frontier region ⊆ p.boundary ℝ

theorem bounds_filledRegion {n : ℕ} (p : Polygon Point2D n) : BoundsRegion p (filledRegion p) :=
  ⟨isClosed_filledRegion p, boundary_subset_filledRegion p, frontier_filledRegion_subset p⟩

end Polygon

namespace FilledPolygonDistance

/-- A connected polygonal path avoiding a region's frontier is entirely
inside or entirely outside that region. -/
private theorem boundary_subset_of_mem {m n : ℕ} [NeZero m]
    (p : Polygon Point2D m) (q : Polygon Point2D n) {Q : Set Point2D}
    (hQ : Polygon.BoundsRegion q Q) (hd : Disjoint (p.boundary ℝ) (q.boundary ℝ))
    (hne : (p.boundary ℝ ∩ Q).Nonempty) : p.boundary ℝ ⊆ Q := by
  have hcover : p.boundary ℝ ⊆ interior Q ∪ Qᶜ := by
    intro X hX
    by_cases hx : X ∈ Q
    · left
      exact (mem_interior_iff_notMem_frontier hx).mpr
        (fun hf => Set.disjoint_left.mp hd hX (hQ.frontier_subset hf))
    · exact Or.inr hx
  rcases (Polygon.isPreconnected_boundary p).subset_or_subset isOpen_interior
    hQ.isClosed.isOpen_compl (Set.disjoint_left.mpr fun _ hi hc => hc (interior_subset hi))
    hcover with h | h
  · exact h.trans interior_subset
  · obtain ⟨X, hX, hXQ⟩ := hne
    exact False.elim (h hX hXQ)

/-- With disjoint boundaries, overlap is detected by any one vertex from
each polygon. The regions need not be convex or simply connected. -/
theorem overlap_iff_vertex_mem {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n)
    {P Q : Set Point2D} (hP : Polygon.BoundsRegion p P)
    (hQ : Polygon.BoundsRegion q Q) (hproper : P ≠ Set.univ)
    (hd : Disjoint (p.boundary ℝ) (q.boundary ℝ)) (i : Fin m) (j : Fin n) :
    (P ∩ Q).Nonempty ↔ p i ∈ Q ∨ q j ∈ P := by
  constructor
  · intro hne
    have hpq : P ∩ Q ≠ Set.univ := by
      intro he
      exact hproper (Set.eq_univ_of_univ_subset (he ▸ Set.inter_subset_left))
    obtain ⟨X, hX⟩ := nonempty_frontier_iff.mpr ⟨hne, hpq⟩
    rcases frontier_inter_subset P Q hX with h | h
    · left
      exact boundary_subset_of_mem p q hQ hd
        ⟨X, hP.frontier_subset h.1, hQ.isClosed.closure_eq ▸ h.2⟩
        (Polygon.vertex_mem_boundary p i)
    · right
      exact boundary_subset_of_mem q p hP hd.symm
        ⟨X, hQ.frontier_subset h.2, hP.isClosed.closure_eq ▸ h.1⟩
        (Polygon.vertex_mem_boundary q j)
  · rintro (h | h)
    · exact ⟨p i, hP.boundary_subset (Polygon.vertex_mem_boundary p i), h⟩
    · exact ⟨q j, h, hQ.boundary_subset (Polygon.vertex_mem_boundary q j)⟩

/-- An exterior point has a nearest frontier point at least as close as any
specified point of the region. -/
theorem exists_frontier_nearer {region : Set Point2D} {X Y : Point2D}
    (hX : X ∉ region) (hY : Y ∈ region) :
    ∃ Z ∈ frontier region, dist X Z ≤ dist X Y := by
  have hne : regionᶜ ≠ Set.univ := by
    intro h
    have : Y ∈ regionᶜ := h ▸ Set.mem_univ Y
    exact this hY
  obtain ⟨Z, hZ, he⟩ := exists_mem_frontier_infDist_compl_eq_dist
    (show X ∈ regionᶜ from hX) hne
  rw [frontier_compl] at hZ
  simp only [compl_compl] at he
  exact ⟨Z, hZ, he ▸ Metric.infDist_le_dist_of_mem hY⟩

/-- For disjoint closed filled regions, the existing boundary expression is
the attained minimum over all pairs of points in the regions. -/
theorem isLeast_of_disjoint {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n)
    {P Q : Set Point2D} (hP : Polygon.BoundsRegion p P)
    (hQ : Polygon.BoundsRegion q Q) (hPQ : Disjoint P Q) :
    IsLeast {r | ∃ X ∈ P, ∃ Y ∈ Q, dist X Y = r}
      (polygonPolygonDistance p q) := by
  constructor
  · obtain ⟨X, hX, Y, hY, he⟩ := (polygon_polygon_isLeast p q).1
    exact ⟨X, hP.boundary_subset hX, Y, hQ.boundary_subset hY, he⟩
  · rintro r ⟨X, hX, Y, hY, rfl⟩
    have hYP : Y ∉ P := fun h => Set.disjoint_left.mp hPQ h hY
    obtain ⟨A, hA, hAY⟩ := exists_frontier_nearer hYP hX
    have hAQ : A ∉ Q := fun h =>
      Set.disjoint_left.mp hPQ (hP.isClosed.frontier_subset hA) h
    obtain ⟨B, hB, hAB⟩ := exists_frontier_nearer hAQ hY
    have h := (polygon_polygon_isLeast p q).2
      ⟨A, hP.frontier_subset hA, B, hQ.frontier_subset hB, rfl⟩
    calc
      polygonPolygonDistance p q ≤ dist A B := h
      _ ≤ dist A Y := hAB
      _ ≤ dist X Y := by simpa only [dist_comm] using hAY

/-- The geometric reduction needed by an interior-membership formula. -/
theorem isLeast {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n)
    {P Q : Set Point2D} (hP : Polygon.BoundsRegion p P)
    (hQ : Polygon.BoundsRegion q Q) :
    IsLeast {r | ∃ X ∈ P, ∃ Y ∈ Q, dist X Y = r}
      (if (P ∩ Q).Nonempty then 0 else polygonPolygonDistance p q) := by
  classical
  split_ifs with h
  · obtain ⟨X, hXP, hXQ⟩ := h
    exact ⟨⟨X, hXP, X, hXQ, dist_self X⟩,
      by rintro r ⟨X, _, Y, _, rfl⟩; exact dist_nonneg⟩
  · exact isLeast_of_disjoint p q hP hQ (Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp h))

end FilledPolygonDistance

/-- Exact distance of two odd–even filled polygons. The local sign product
tests one vertex of each path against the other filled region. Crossing or
touching paths already have zero boundary distance. All coordinates may be
arbitrary real values, including degenerate and self-intersecting paths. -/
def filledPolygonDistance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) : ℝ :=
  let inside := fun {k : ℕ} (r : Polygon Point2D k) (X : Point2D) =>
    let positive := fun x : ℝ => (Real.sign x ^ 2 + Real.sign x) / 2
    let parity := ∏ i : Fin k,
      let A := r i
      let B := r (finRotate k i)
      let a := A 1 - X 1
      let b := B 1 - X 1
      let det := (A 0 - X 0) * b - a * (B 0 - X 0)
      let crossing := (positive a - positive b) ^ 2 * positive (det * (B 1 - A 1))
      1 - 2 * crossing
    (1 - parity) / 2
  (1 - inside p (q 0)) * (1 - inside q (p 0)) * polygonPolygonDistance p q

theorem filledPolygonDistance_eq {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    filledPolygonDistance p q =
      (1 - Polygon.oddEvenIndicator p (q 0)) *
        (1 - Polygon.oddEvenIndicator q (p 0)) * polygonPolygonDistance p q := rfl

/-- The symbolic correction is zero exactly when the filled regions overlap;
otherwise it leaves the boundary distance unchanged. -/
theorem filledPolygonDistance_eq_ite {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    filledPolygonDistance p q =
      if (Polygon.filledRegion p ∩ Polygon.filledRegion q).Nonempty
      then 0 else polygonPolygonDistance p q := by
  by_cases hz : polygonPolygonDistance p q = 0
  · obtain ⟨X, hX, hY⟩ := (polygonPolygonDistance_eq_zero_iff p q).mp hz
    have hne : (Polygon.filledRegion p ∩ Polygon.filledRegion q).Nonempty :=
      ⟨X, Polygon.boundary_subset_filledRegion p hX, Polygon.boundary_subset_filledRegion q hY⟩
    simp [filledPolygonDistance_eq, hz, hne]
  · have hd : Disjoint (p.boundary ℝ) (q.boundary ℝ) :=
      Set.disjoint_left.mpr fun X hX hY =>
        hz ((polygonPolygonDistance_eq_zero_iff p q).mpr ⟨X, hX, hY⟩)
    have hp : p 0 ∉ q.boundary ℝ :=
      fun h => Set.disjoint_left.mp hd (Polygon.vertex_mem_boundary p 0) h
    have hq : q 0 ∉ p.boundary ℝ :=
      fun h => Set.disjoint_left.mp hd h (Polygon.vertex_mem_boundary q 0)
    have he := FilledPolygonDistance.overlap_iff_vertex_mem p q
      (Polygon.bounds_filledRegion p) (Polygon.bounds_filledRegion q)
      (Polygon.filledRegion_ne_univ p) hd 0 0
    simp only [Polygon.filledRegion, Set.mem_union, Set.mem_ofPred_eq, hp, hq, false_or] at he
    change (Polygon.filledRegion p ∩ Polygon.filledRegion q).Nonempty ↔
      Polygon.oddEvenIndicator q (p 0) = 1 ∨ Polygon.oddEvenIndicator p (q 0) = 1 at he
    rw [filledPolygonDistance_eq, he]
    rcases Polygon.oddEvenIndicator_cases p (q 0) with hi | hi <;>
      rcases Polygon.oddEvenIndicator_cases q (p 0) with hj | hj <;> simp [hi, hj]

/-- The formula attains the minimum of point-to-point distances over the
complete filled regions, not only their polygonal paths. -/
theorem filled_polygon_isLeast {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    IsLeast {r | ∃ X ∈ Polygon.filledRegion p, ∃ Y ∈ Polygon.filledRegion q, dist X Y = r}
      (filledPolygonDistance p q) := by
  rw [filledPolygonDistance_eq_ite]
  exact FilledPolygonDistance.isLeast p q
    (Polygon.bounds_filledRegion p) (Polygon.bounds_filledRegion q)

theorem filled_polygon_distance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    distance (Polygon.filledRegion p) (Polygon.filledRegion q) = filledPolygonDistance p q :=
  (filled_polygon_isLeast p q).csInf_eq

theorem filledPolygonDistance_nonneg {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) : 0 ≤ filledPolygonDistance p q := by
  obtain ⟨X, _, Y, _, he⟩ := (filled_polygon_isLeast p q).1
  exact he ▸ dist_nonneg

theorem filledPolygonDistance_comm {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    filledPolygonDistance p q = filledPolygonDistance q p := by
  rw [filledPolygonDistance_eq, filledPolygonDistance_eq, polygonPolygonDistance_comm p q]
  ring

theorem filledPolygonDistance_eq_zero_iff {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    filledPolygonDistance p q = 0 ↔
      (Polygon.filledRegion p ∩ Polygon.filledRegion q).Nonempty := by
  constructor
  · intro h
    obtain ⟨X, hX, Y, hY, he⟩ := (filled_polygon_isLeast p q).1
    have hXY := dist_eq_zero.mp (he.trans h)
    exact ⟨X, hX, hXY ▸ hY⟩
  · intro h
    simp [filledPolygonDistance_eq_ite, h]

/-- The same filled distance, expressed through winding-number parity. The
factor `(1 + cos (π*w)) / 2` is one for even winding and zero for odd winding.
At query vertices on the other path, boundary distance is already zero. -/
def windingPolygonDistance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) : ℝ :=
  let wp := Polygon.windingNumber p (q 0)
  let wq := Polygon.windingNumber q (p 0)
  let outsideP := (1 + Real.cos ((wp : ℝ) * Real.pi)) / 2
  let outsideQ := (1 + Real.cos ((wq : ℝ) * Real.pi)) / 2
  outsideP * outsideQ * polygonPolygonDistance p q

theorem windingPolygonDistance_eq_filledPolygonDistance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    windingPolygonDistance p q = filledPolygonDistance p q := by
  by_cases hz : polygonPolygonDistance p q = 0
  · simp [windingPolygonDistance, filledPolygonDistance_eq, hz]
  · have hp : q 0 ∉ p.boundary ℝ := fun h =>
      hz ((polygonPolygonDistance_eq_zero_iff p q).mpr
        ⟨q 0, h, Polygon.vertex_mem_boundary q 0⟩)
    have hq : p 0 ∉ q.boundary ℝ := fun h =>
      hz ((polygonPolygonDistance_eq_zero_iff p q).mpr
        ⟨p 0, Polygon.vertex_mem_boundary p 0, h⟩)
    rw [filledPolygonDistance_eq, Polygon.oddEvenIndicator_eq_windingNumber p hp,
      Polygon.oddEvenIndicator_eq_windingNumber q hq]
    unfold windingPolygonDistance
    ring

/-- The winding-number formula attains the minimum over all pairs of points
in the two regions of odd winding, including the polygonal paths. -/
theorem winding_filled_polygon_isLeast {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    IsLeast {r | ∃ X ∈ Polygon.windingFilledRegion p,
      ∃ Y ∈ Polygon.windingFilledRegion q, dist X Y = r} (windingPolygonDistance p q) := by
  rw [windingPolygonDistance_eq_filledPolygonDistance,
    Polygon.windingFilledRegion_eq_filledRegion, Polygon.windingFilledRegion_eq_filledRegion]
  exact filled_polygon_isLeast p q

theorem winding_filled_polygon_distance {m n : ℕ} [NeZero m] [NeZero n]
    (p : Polygon Point2D m) (q : Polygon Point2D n) :
    distance (Polygon.windingFilledRegion p) (Polygon.windingFilledRegion q) =
      windingPolygonDistance p q := (winding_filled_polygon_isLeast p q).csInf_eq

/-- Strict containment is detected even when the boundaries do not meet. -/
theorem filledPolygonDistance_nested :
    filledPolygonDistance
      (Polygon.ofVertices [!₂[0, 0], !₂[4, 0], !₂[4, 4], !₂[0, 4]])
      (Polygon.ofVertices [!₂[1, 1], !₂[2, 1], !₂[2, 2], !₂[1, 2]]) = 0 := by
  rw [filledPolygonDistance_eq]
  have hi : Polygon.oddEvenIndicator
      (Polygon.ofVertices [!₂[0, 0], !₂[4, 0], !₂[4, 4], !₂[0, 4]]) !₂[1, 1] = 1 := by
    simp only [Polygon.oddEvenIndicator, Polygon.ofVertices, List.length_cons, List.length_nil]
    norm_num [Fin.prod_univ_succ, Real.sign]
  change (1 - Polygon.oddEvenIndicator _ !₂[1, 1]) * _ * _ = 0
  rw [hi]
  ring

end

end SympyGeometry
