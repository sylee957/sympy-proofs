module

public import SympyProofs.Geometry.PointConicDistance
public import Mathlib.Geometry.Polygon.Basic

/-!
# An ordered-path model of SymPy polygons

SymPy's `geometry/polygon.py` stores an ordered sequence of two-dimensional
vertices, joins the last vertex back to the first, and treats the polygon as
its boundary. Self-intersections are allowed and `area` is signed.
Mathlib's `Polygon Point2D n` already supplies this representation.

This models real-valued vertex data and the boundary, perimeter, and area
formulas. It deliberately also admits unnormalized and degenerate vertex
sequences. Symbolic real coordinates can be Lean variables; SymPy expressions
and its partial decisions about equality or collinearity are not modeled.
The Python constructor's duplicate/collinear-vertex removal, dispatch to
`Point`, `Segment`, or `Triangle`, and `RegularPolygon` constructor are separate
from this representation and are not implemented here.

Lean equality retains the vertex order. SymPy's `_hashable_content` identifies
cyclic shifts and reversal, although reversal changes signed area; that
comparison must be a separate relation, not Lean equality on this data.
-/

@[expose] public section

namespace SympyGeometry

namespace Polygon

variable {n : ℕ}

/-- Import an ordered vertex list without performing constructor normalization. -/
def ofVertices (vertices : List Point2D) : Polygon Point2D vertices.length :=
  ⟨fun i => vertices[i]⟩

/-- Mathlib's edges are exactly the segments already used in `SympyGeometry`. -/
theorem edgeSet_eq_segment (p : Polygon Point2D n) (i : Fin n) :
    p.edgeSet ℝ i = segment (p i) (p (finRotate n i)) := by
  simp only [_root_.Polygon.edgeSet, affineSegment, segment,
    AffineMap.lineMap_apply_module]

/-- Point membership means lying on at least one side, including the closing side. -/
theorem mem_boundary_iff (p : Polygon Point2D n) (X : Point2D) :
    X ∈ p.boundary ℝ ↔ ∃ i : Fin n, X ∈ segment (p i) (p (finRotate n i)) := by
  simp only [_root_.Polygon.boundary, Set.mem_iUnion, edgeSet_eq_segment]

theorem vertex_mem_boundary (p : Polygon Point2D n) (i : Fin n) :
    p i ∈ p.boundary ℝ := by
  rw [mem_boundary_iff]
  exact ⟨i, 0, by norm_num, by simp⟩

/-- SymPy's signed shoelace area, summing each vertex with its successor. -/
noncomputable def signedArea (p : Polygon Point2D n) : ℝ :=
  (∑ i : Fin n, (p i 0 * p (finRotate n i) 1 - p (finRotate n i) 0 * p i 1)) / 2

/-- Reindexing gives the predecessor/current-vertex loop in `Polygon.area`. -/
theorem signedArea_eq_predecessor_sum (p : Polygon Point2D n) :
    signedArea p =
      (∑ i : Fin n, (p ((finRotate n).symm i) 0 * p i 1 -
        p i 0 * p ((finRotate n).symm i) 1)) / 2 := by
  unfold signedArea
  congr 1
  simpa only [Equiv.symm_apply_apply] using Equiv.sum_comp (finRotate n)
    (fun i => p ((finRotate n).symm i) 0 * p i 1 -
      p i 0 * p ((finRotate n).symm i) 1)

/-- The sum of Euclidean side lengths, including the closing side. -/
noncomputable def perimeter (p : Polygon Point2D n) : ℝ :=
  ∑ i : Fin n, dist (p i) (p (finRotate n i))

theorem perimeter_nonneg (p : Polygon Point2D n) : 0 ≤ perimeter p :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- Reindexing gives the predecessor/current-vertex loop in `Polygon.perimeter`. -/
theorem perimeter_eq_predecessor_sum (p : Polygon Point2D n) :
    perimeter p = ∑ i : Fin n, dist (p ((finRotate n).symm i)) (p i) := by
  simpa only [perimeter, Equiv.symm_apply_apply] using Equiv.sum_comp (finRotate n)
    (fun i => dist (p ((finRotate n).symm i)) (p i))

/-- A triangle has the usual oriented determinant area, for arbitrary real coordinates. -/
theorem signedArea_triangle (A B C : Point2D) :
    signedArea (ofVertices [A, B, C]) =
      ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) / 2 := by
  simp [signedArea, ofVertices, Fin.sum_univ_succ]
  ring

/-- Symbolic real side lengths are supported without an expression AST. -/
theorem signedArea_rectangle (a b : ℝ) :
    signedArea (ofVertices [!₂[0, 0], !₂[a, 0], !₂[a, b], !₂[0, b]]) = a * b := by
  simp [signedArea, ofVertices, Fin.sum_univ_succ]

/-- Reversing the rectangle's traversal changes the sign. -/
theorem signedArea_rectangle_clockwise (a b : ℝ) :
    signedArea (ofVertices [!₂[0, 0], !₂[0, b], !₂[a, b], !₂[a, 0]]) = -(a * b) := by
  simp [signedArea, ofVertices, Fin.sum_univ_succ]

/-- SymPy's crossing Z-shaped example has cancelling signed-area contributions. -/
theorem signedArea_crossed :
    signedArea (ofVertices [!₂[0, 2], !₂[2, 2], !₂[0, 0], !₂[2, 0]]) = 0 := by
  simp [signedArea, ofVertices, Fin.sum_univ_succ]

end Polygon

end SympyGeometry
