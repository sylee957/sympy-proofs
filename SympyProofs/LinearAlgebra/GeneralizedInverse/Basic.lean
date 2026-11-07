module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Projection

/-! Reflexive generalized inverses of rectangular matrices and uniqueness from
their range and kernel, including existence for prescribed complementary submodules. -/

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

theorem IsReflexiveGeneralizedInverse.symm
    {A : Matrix m n R} {G : Matrix n m R}
    (h : IsReflexiveGeneralizedInverse A G) : IsReflexiveGeneralizedInverse G A :=
  ⟨h.outer, h.inner⟩

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

/-- The range of a reflexive generalized inverse complements the original kernel. -/
theorem IsReflexiveGeneralizedInverse.isCompl_ker_range
    {A : Matrix m n R} {G : Matrix n m R}
    (h : IsReflexiveGeneralizedInverse A G) :
    IsCompl (LinearMap.ker A.mulVecLin) (LinearMap.range G.mulVecLin) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    change A.mulVec (G.mulVec y) = 0 at hx
    have hy := congrArg G.mulVec hx
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h.outer, Matrix.mulVec_zero,
      Matrix.mulVecLin_apply] using hy
  · rw [codisjoint_iff_le_sup]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x - G.mulVec (A.mulVec x), ?_, G.mulVec (A.mulVec x),
      LinearMap.mem_range_self G.mulVecLin _, sub_add_cancel _ _⟩
    change A.mulVec (x - G.mulVec (A.mulVec x)) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.inner, sub_self]

/-- The kernel of a reflexive generalized inverse complements the original range. -/
theorem IsReflexiveGeneralizedInverse.isCompl_range_ker
    {A : Matrix m n R} {G : Matrix n m R}
    (h : IsReflexiveGeneralizedInverse A G) :
    IsCompl (LinearMap.range A.mulVecLin) (LinearMap.ker G.mulVecLin) :=
  h.symm.isCompl_ker_range.symm

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

/-- If the domain decomposes as `ker A ⊕ T` and the codomain as `range A ⊕ S`,
there is exactly one reflexive generalized inverse with range `T` and kernel `S`.
It inverts `A` on `T` and vanishes on `S`. -/
theorem existsUnique_reflexiveGeneralizedInverse_of_isCompl
    (A : Matrix m n R) (T : Submodule R (n → R)) (S : Submodule R (m → R))
    (hT : IsCompl (LinearMap.ker A.mulVecLin) T)
    (hS : IsCompl (LinearMap.range A.mulVecLin) S) :
    ∃! G : Matrix n m R,
      IsReflexiveGeneralizedInverse A G ∧
        LinearMap.range G.mulVecLin = T ∧ LinearMap.ker G.mulVecLin = S := by
  classical
  let i := A.mulVecLin.domRestrict T
  have hi : Function.Injective i :=
    LinearMap.injective_domRestrict_iff.mpr hT.symm.disjoint
  have hirange : LinearMap.range i = LinearMap.range A.mulVecLin := by
    have hzero : (LinearMap.ker A.mulVecLin).map A.mulVecLin = ⊥ :=
      LinearMap.le_ker_iff_map.mp le_rfl
    calc
      LinearMap.range i = T.map A.mulVecLin := LinearMap.range_domRestrict _ _
      _ = ((LinearMap.ker A.mulVecLin) ⊔ T).map A.mulVecLin := by
        rw [Submodule.map_sup, hzero, bot_sup_eq]
      _ = LinearMap.range A.mulVecLin := by rw [hT.sup_eq_top, Submodule.map_top]
  have hiS : IsCompl (LinearMap.range i) S := hirange.symm ▸ hS
  let p := LinearMap.linearProjOfIsCompl S i hi hiS
  have hp (t : T) : p (i t) = t := LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ _
  let g := T.subtype.comp p
  have hgrange : LinearMap.range g = T := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (p x).property
    · intro hy
      refine ⟨i ⟨y, hy⟩, ?_⟩
      change (p (i ⟨y, hy⟩) : n → R) = y
      rw [hp]
  have hgker : LinearMap.ker g = S := by
    rw [LinearMap.ker_comp_of_ker_eq_bot p (LinearMap.ker_eq_bot.mpr T.subtype_injective)]
    exact LinearMap.ker_linearProjOfIsCompl _ _ _ _
  let G := LinearMap.toMatrix' g
  have hGlin : G.mulVecLin = g := Matrix.toLin'_toMatrix' g
  have hG : IsReflexiveGeneralizedInverse A G := by
    constructor
    · apply Matrix.ext_iff_mulVec.mpr
      intro x
      have hx : A.mulVec x ∈ LinearMap.range i := by
        rw [hirange]
        exact LinearMap.mem_range_self A.mulVecLin x
      obtain ⟨t, ht⟩ := hx
      simp only [G, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      rw [← ht]
      change i (p (i t)) = i t
      rw [hp]
    · apply Matrix.ext_iff_mulVec.mpr
      intro x
      simp only [G, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      change (p (i (p x)) : n → R) = (p x : n → R)
      rw [hp]
  refine ⟨G, ⟨hG, hGlin ▸ hgrange, hGlin ▸ hgker⟩, ?_⟩
  rintro H ⟨hH, hHrange, hHker⟩
  apply hH.eq_of_range_eq_of_ker_eq hG
  · rw [hHrange, hGlin, hgrange]
  · rw [hHker, hGlin, hgker]

end CommRing

end Matrix
