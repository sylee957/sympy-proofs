module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Coefficients

/-! Projecting the final lower elementary subspace to the original input coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- The lower elementary subspace in a fixed coordinate space. -/
theorem elementaryBasis_iff_span {t : Tower R n} {lower : Level R n}
    (hl : lower.ElementaryBasisSpec k t) (gs : List (K R n)) (cs : List k) (m : ℕ)
    (hm : cs.length = m) (hg : gs.length = m) :
    t.Elementary k (Model.linearCombination k cs gs) ↔
      Linear.vector (RingHom.id k) m cs ∈ Submodule.span k
        ((fun w : List (K R 0) × Answer R n => Linear.vector (Model.constantHom k) m w.1) ''
          {w | w ∈ lower.elementaryBasis gs}) := by
  subst m
  have eqn : (fun r : List (K R 0) => Linear.vector (Model.constantHom k) cs.length r) ''
        {r | r ∈ (lower.elementaryBasis gs).map Prod.fst} =
      ((fun w : List (K R 0) × Answer R n => Linear.vector (Model.constantHom k) cs.length w.1) ''
        {w | w ∈ lower.elementaryBasis gs}) := by
    ext u
    constructor
    · rintro ⟨r,hr,rfl⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
      exact ⟨_,hw,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.1, List.mem_map_of_mem hw,rfl⟩
  rw [← eqn]
  exact (hl gs).2 cs hg.symm

/-- Given a family of columns, projecting the integrable residual directions gives precisely
the input coordinates with an integrable coefficient at the reserved Laurent power. -/
theorem projected_elementary_iff {t : Tower R n} {lower : Level R n}
    (hl : lower.ElementaryBasisSpec k t) (w s : ℕ) (cols : List (Column R n)) (x : Fin w → k) :
    x ∈ Submodule.span k ((fun z : List (K R 0) × Answer R n =>
        Linear.vector (Model.constantHom k) w (combine w cols z.1).params) ''
          {z | z ∈ lower.elementaryBasis (cols.map fun v => v.residual.coeff s)}) ↔
      ∃ z : State k n w, z ∈ Submodule.span k (Column.value k w '' {c | c ∈ cols}) ∧
        x = z.1 ∧ t.Elementary k (z.2.2.coeff s) := by
  let gs := cols.map fun v => v.residual.coeff s
  let bs := lower.elementaryBasis gs
  let u := fun p : List (K R 0) × Answer R n => Linear.vector (Model.constantHom k) cols.length p.1
  let T := (LinearMap.fst k _ _).comp (Linear.accumulate cols (Column.value k w))
  let v := fun p : List (K R 0) × Answer R n =>
    Linear.vector (Model.constantHom k) w (combine w cols p.1).params
  have he := Linear.mem_mapped_columns_iff bs u id v T (fun q _ =>
    congrArg Prod.fst (value_combine k w cols q.1)) x
  simp only [List.map_id] at he
  change x ∈ Submodule.span k (v '' {b | b ∈ bs}) ↔ _
  rw [he]
  have hp (a : Fin cols.length → k) :
      a ∈ Submodule.span k (u '' {b | b ∈ bs}) ↔
        t.Elementary k ((Linear.accumulate cols (Column.value k w) a).2.2.coeff s) := by
    have elem := elementaryBasis_iff_span k hl gs (List.ofFn a) cols.length
      List.length_ofFn (List.length_map ..)
    have hv : Linear.vector (RingHom.id k) cols.length (List.ofFn a) = a := by
      ext i
      simp [Linear.vector, List.getD_eq_getElem?_getD]
    rw [hv] at elem
    rw [residual_coeff]
    exact elem.symm
  constructor
  · rintro ⟨a,ha,hx⟩
    exact ⟨_, (Linear.mem_columns_iff cols _ _).mpr ⟨a,rfl⟩, hx.symm, (hp a).mp ha⟩
  · rintro ⟨z,hz,hx,h⟩
    obtain ⟨a,rfl⟩ := (Linear.mem_columns_iff cols _ z).mp hz
    exact ⟨a,(hp a).mpr h,hx.symm⟩

end SympyProofs.Calculus.Antiderivative.Elementary
