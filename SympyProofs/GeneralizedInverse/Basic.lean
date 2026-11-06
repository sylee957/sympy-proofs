module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Reflexive generalized inverses of rectangular matrices and uniqueness from
their range and kernel. -/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section Semiring

variable {R : Type*} [Semiring R]

/-- A reflexive generalized inverse satisfies both `A * G * A = A` and
`G * A * G = G`. -/
structure IsReflexiveGeneralizedInverse (A : Matrix m n R) (G : Matrix n m R) : Prop where
  inner : A * G * A = A
  outer : G * A * G = G

theorem IsReflexiveGeneralizedInverse.left_idempotent
    {A : Matrix m n R} {G : Matrix n m R}
    (h : IsReflexiveGeneralizedInverse A G) : (A * G) * (A * G) = A * G := by
  rw [← Matrix.mul_assoc, h.inner]

theorem IsReflexiveGeneralizedInverse.right_idempotent
    {A : Matrix m n R} {G : Matrix n m R}
    (h : IsReflexiveGeneralizedInverse A G) : (G * A) * (G * A) = G * A := by
  rw [← Matrix.mul_assoc, h.outer]

/-- Reflexive generalized inverses agree when both products with the original
matrix agree. -/
theorem IsReflexiveGeneralizedInverse.eq_of_mul_eq
    {A : Matrix m n R} {G H : Matrix n m R}
    (hG : IsReflexiveGeneralizedInverse A G) (hH : IsReflexiveGeneralizedInverse A H)
    (hGA : G * A = H * A) (hAG : A * G = A * H) : G = H := by
  calc
    G = G * A * G := hG.outer.symm
    _ = H * A * G := by rw [hGA]
    _ = H * A * H := by rw [Matrix.mul_assoc, hAG, ← Matrix.mul_assoc]
    _ = H := hH.outer

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- A reflexive generalized inverse is uniquely determined by its range and
kernel, for a fixed original matrix. -/
theorem IsReflexiveGeneralizedInverse.eq_of_range_eq_of_ker_eq
    {A : Matrix m n R} {G H : Matrix n m R}
    (hG : IsReflexiveGeneralizedInverse A G) (hH : IsReflexiveGeneralizedInverse A H)
    (hrange : LinearMap.range G.mulVecLin = LinearMap.range H.mulVecLin)
    (hker : LinearMap.ker G.mulVecLin = LinearMap.ker H.mulVecLin) : G = H := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  have hx : G.mulVec x ∈ LinearMap.range H.mulVecLin := by
    rw [← hrange]
    exact LinearMap.mem_range_self G.mulVecLin x
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
  change H.mulVec y = G.mulVec x at hy
  have hz : A.mulVec (G.mulVec x) - x ∈ LinearMap.ker G.mulVecLin := by
    change G.mulVec (A.mulVec (G.mulVec x) - x) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG.outer, sub_self]
  rw [hker] at hz
  calc
    G.mulVec x = H.mulVec (A.mulVec (G.mulVec x)) := by
      rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH.outer]
    _ = H.mulVec x := by
      simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub,
        sub_eq_zero] using hz

end CommRing

end Matrix
