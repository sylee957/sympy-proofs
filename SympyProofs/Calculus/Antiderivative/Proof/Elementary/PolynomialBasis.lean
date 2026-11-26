module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Columns
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Criterion
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Projection
public import SympyProofs.Calculus.Antiderivative.Spec.Split

/-! Correctness of all directions and answers returned by parametric polynomial integration. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Joining a polynomial over a power of the generator interprets it as its Laurent numerator. -/
theorem val_join_shift (p : Poly (K R n)) (s : ℕ) :
    val k (K.join p (Poly.X^s)) = laurentValue k s (modelPoly k p) := by
  apply (Model.stepEquiv k n).injective
  simp [K.join, laurentValue, val_joinPoly, modelPoly]

private theorem ofFn_vector {F : Type} [Field F] (f : F →+* k) (m : ℕ) (r : List F)
    (h : r.length = m) : List.ofFn (Linear.vector f m r) = r.map f := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi _
    have hi' : i < r.length := by simpa [h] using hi
    simp [Linear.vector, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

/-- Each returned polynomial direction has a regular primitive of the corresponding input
combination. Its vector has exactly one entry per input polynomial. -/
theorem polynomialBasis_sound {t : Tower R n} {lower : Level R n} (hl : lower.SolveSpec k t)
    (he : lower.ElementaryBasisSpec k t) (g : ReducedGen (K R n)) (s : ℕ) (hs : LawfulShift g s)
    (ps : List (Poly (K R n))) (out : List (K R 0) × Answer R (n+1))
    (hout : out ∈ polynomialBasis t.D g lower s ps) :
    out.1.length = ps.length ∧ out.2.Regular k ∧ out.2.deriv k (t.step g) =
      laurentValue k s (Linear.accumulate ps (modelPoly k)
        (Linear.vector (Model.constantHom k) ps.length out.1)) := by
  let cols := polynomialColumns t g lower s ps
  let gs := cols.map fun v => v.residual.coeff s
  obtain ⟨⟨c,ans⟩,hc,rfl⟩ := List.mem_map.mp hout
  change (c,ans) ∈ lower.elementaryBasis gs at hc
  obtain ⟨hlen,hr,hd⟩ := (he gs).1 _ hc
  let col := combine ps.length cols c
  let z := col.value k ps.length
  let P := Linear.accumulate ps (modelPoly k) z.1
  have hz : z ∈ Submodule.span k (Column.value k ps.length '' {v | v ∈ cols}) :=
    (Linear.mem_columns_iff cols _ _).mpr ⟨_,(value_combine k ps.length cols c).symm⟩
  obtain ⟨_,_,hres,hmono⟩ := (mem_polynomialColumns_iff k hl g s ps z).mp hz
  have h₀ : z.2.2.coeff s = ans.deriv k t := by
    change ((combine ps.length cols c).value k ps.length).2.2.coeff s = _
    rw [value_combine, residual_coeff, ofFn_vector]
    · exact hd.symm
    · simpa [gs] using hlen
  have hP : monomial s (ans.deriv k t) + laurentOp k t g s z.2.1 = P := by
    rw [← h₀, ← hmono, hres]
    exact sub_add_cancel ..
  change col.params.length = ps.length ∧
    (ans.lift.addField (K.join col.solution (Poly.X ^ s))).Regular k ∧
    (ans.lift.addField (K.join col.solution (Poly.X ^ s))).deriv k (t.step g) =
      laurentValue k s P
  refine ⟨by simp [col, combine, coordinates], (Answer.regular_addField ..).mpr
    ((Answer.regular_lift ..).mpr hr), ?_⟩
  rw [Answer.deriv_addField, Answer.deriv_lift, val_join_shift, deriv_laurentValue k t g s hs,
    ← laurentValue_monomial k s, ← laurentValue_add, ← hP]
  rfl

/-- After extending the constants, the computed directions span exactly the integrable
linear combinations of the input polynomials at the given Laurent shift. -/
theorem polynomialBasis_complete [CharZero k] {t : Tower R n} {lower : Level R n}
    (hl : lower.SolveSpec k t) (he : lower.ElementaryBasisSpec k t) (ht : t.Admissible k)
    (g : ReducedGen (K R n)) (hg : g.Admissible k t) (s : ℕ) (hs : LawfulShift g s)
    (ps : List (Poly (K R n))) (x : Fin ps.length → k) :
    x ∈ Submodule.span k
      ((fun z : List (K R 0) × Answer R (n+1) =>
        Linear.vector (Model.constantHom k) ps.length z.1) ''
        {z | z ∈ polynomialBasis t.D g lower s ps}) ↔
      (t.step g).Elementary k (laurentValue k s (Linear.accumulate ps (modelPoly k) x)) := by
  let cols := polynomialColumns t g lower s ps
  let P := Linear.accumulate ps (modelPoly k) x
  let gs := cols.map fun v => v.residual.coeff s
  let H := fun z : List (K R 0) × Answer R (n+1) =>
    Linear.vector (Model.constantHom k) ps.length z.1
  let V := fun z : List (K R 0) × Answer R n =>
    Linear.vector (Model.constantHom k) ps.length (combine ps.length cols z.1).params
  have eqn : H '' {z | z ∈ polynomialBasis t.D g lower s ps} =
      V '' {z | z ∈ lower.elementaryBasis gs} := by
    ext v
    constructor
    · rintro ⟨out,h,rfl⟩
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨_, List.mem_map_of_mem hq,rfl⟩
  change x ∈ Submodule.span k (H '' _) ↔ _
  rw [eqn, projected_elementary_iff k he, elementary_iff_correction k t g ht hg s (size ps)
    hs _ (accumulate_below k ps x)]
  constructor
  · rintro ⟨z,hz,hx,hlo⟩
    obtain ⟨hb,h₀,hr,hm⟩ := (mem_polynomialColumns_iff k hl g s ps z).mp hz
    refine ⟨z.2.1,z.2.2.coeff s,hb,h₀,hlo,?_⟩
    rw [hx, ← hm, hr]
    exact (add_sub_cancel ..).symm
  · rintro ⟨q,r,hb,h₀,hlo,hr⟩
    let z : State k n ps.length := (x,q,monomial s r)
    have hz : z ∈ Submodule.span k (Column.value k ps.length '' {v | v ∈ cols}) := by
      apply (mem_polynomialColumns_iff k hl g s ps z).mpr
      refine ⟨hb,h₀,?_,by simp [z]⟩
      change monomial s r = Linear.accumulate ps (modelPoly k) x - _
      rw [hr, add_sub_cancel_left]
    exact ⟨z,hz,rfl,by simpa [z] using hlo⟩

end SympyProofs.Calculus.Antiderivative.Elementary
