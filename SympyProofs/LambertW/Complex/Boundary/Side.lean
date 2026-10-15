import Mathlib.Analysis.Complex.Convex

/-! # Shared boundary-side convention -/
namespace LambertW.Complex
open Set Filter Topology

/-- Which side of the negative real cut supplies its boundary value. -/
inductive BoundarySide
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Conjugation exchanges the sides of the cut. -/
def BoundarySide.opposite : BoundarySide → BoundarySide
  | .upper => .lower
  | .lower => .upper

@[simp] theorem BoundarySide.opposite_opposite (side : BoundarySide) :
    side.opposite.opposite = side := by cases side <;> rfl

/-- The open half-plane from which the chosen boundary values are approached. -/
def BoundarySide.halfPlane : BoundarySide → Set ℂ
  | .upper => {z | 0 < z.im}
  | .lower => {z | z.im < 0}

/-- Every real point is approached by points in either open half-plane.
This ensures uniqueness of the corresponding limits is not vacuous. -/
theorem BoundarySide.nhdsWithin_halfPlane_neBot (side : BoundarySide) (x : ℝ) :
    NeBot (𝓝[side.halfPlane] (x : ℂ)) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  cases side with
  | upper =>
    have hp : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝[BoundarySide.upper.halfPlane] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (tendsto_const_nhds (x := (x : ℂ))).add (ht.mul_const Complex.I)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [BoundarySide.halfPlane] using ht
    exact hp.neBot
  | lower =>
    have hp : Tendsto (fun t : ℝ => (x : ℂ) - (t : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝[BoundarySide.lower.halfPlane] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (tendsto_const_nhds (x := (x : ℂ))).sub (ht.mul_const Complex.I)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [BoundarySide.halfPlane] using ht
    exact hp.neBot

end LambertW.Complex
