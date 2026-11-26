module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.DirectionCombination
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.DirectionSpec

/-! Combining the normal-residue and polynomial subspaces gives the parametric elementary
integration specification over arbitrary model constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

theorem fromDirections_sound {t : Tower R n} {g : ReducedGen (K R n)} {lower : Level R n}
    (hl : lower.SolveSpec k t) (he : lower.ElementaryBasisSpec k t)
    {gs : List (K R (n+1))} {s : ℕ} {ds : List (Direction R n)}
    (hd : DirectionSpec k t g gs s ds) (hs : LawfulShift g s)
    (out : List (K R 0) × Answer R (n+1)) (hout : out ∈ fromDirections t.D g lower gs.length s ds) :
    out.1.length = gs.length ∧ out.2.Regular k ∧
      out.2.deriv k (t.step g) =
        Model.linearCombination k (out.1.map (Model.constantHom k)) gs := by
  obtain ⟨⟨q,ans⟩,hq,rfl⟩ := List.mem_map.mp hout
  obtain ⟨_,hreg,han⟩ := polynomialBasis_sound k hl he g s hs _ _ hq
  dsimp only at han hreg ⊢
  have hwidth : (coordinates gs.length q (ds.map Direction.coords)).length = gs.length := by
    simp [coordinates]
  refine ⟨hwidth,(Answer.regular_add ..).mpr ⟨hreg,?_⟩,?_⟩
  · apply Answer.combine_regular k (t.step g)
    simpa using hd.regular
  · rw [Answer.deriv_add, Answer.combine_deriv, ← Model.accumulate_constants k _ _ hwidth,
      Linear.vector_coordinates, hd.combination_identity, han, Linear.accumulate_vector_map,
      Linear.accumulate_vector_map]
    exact add_comm ..

theorem fromDirections_complete [CharZero k] {t : Tower R n} {g : ReducedGen (K R n)}
    {lower : Level R n}
    (hl : lower.SolveSpec k t) (he : lower.ElementaryBasisSpec k t)
    (ht : t.Admissible k) (hg : g.Admissible k t)
    {gs : List (K R (n+1))} {s : ℕ} {ds : List (Direction R n)}
    (hd : DirectionSpec k t g gs s ds) (hs : LawfulShift g s) (cs : List k)
    (hc : cs.length = gs.length) :
    (t.step g).Elementary k (Model.linearCombination k cs gs) ↔
      Linear.vector (RingHom.id k) gs.length cs ∈ Submodule.span k
        ((fun w : List (K R 0) × Answer R (n+1) =>
          Linear.vector (Model.constantHom k) gs.length w.1) ''
          {w | w ∈ fromDirections t.D g lower gs.length s ds}) := by
  let ps := ds.map Direction.rest
  let bs := polynomialBasis t.D g lower s ps
  let u := fun z : List (K R 0) × Answer R (n+1) =>
    Linear.vector (Model.constantHom k) ps.length z.1
  let E := finCongr (List.length_map (f := Direction.rest) (as := ds))
  let castV : (Fin ps.length → k) →ₗ[k] (Fin ds.length → k) :=
    LinearMap.pi fun i => LinearMap.proj (E.symm i)
  let toInput := Linear.accumulate (k := k) ds
    (fun d => Linear.vector (Model.constantHom k) gs.length d.coords)
  let T := toInput.comp castV
  let x := Linear.vector (RingHom.id k) gs.length cs
  let fn := fun z : List (K R 0) × Answer R (n+1) =>
    (coordinates gs.length z.1 (ds.map Direction.coords), z.2.add (Answer.combine z.1
      (ds.map Direction.answer)))
  let v := fun z : List (K R 0) × Answer R (n+1) =>
    Linear.vector (Model.constantHom k) gs.length z.1
  have hv (z : List (K R 0) × Answer R (n+1)) : v (fn z) = T (u z) := by
    change Linear.vector (Model.constantHom k) _ (coordinates _ _ _) = _
    rw [Linear.vector_coordinates]
    rfl
  change _ ↔ x ∈ Submodule.span k (v '' {b | b ∈ bs.map fn})
  rw [Linear.mem_mapped_columns_iff bs u fn v T (fun z _ => hv z)]
  have hp (a : Fin ps.length → k) : a ∈ Submodule.span k (u '' {z | z ∈ bs}) ↔
      (t.step g).Elementary k (Linear.accumulate gs (val k) (T a)) := by
    rw [polynomialBasis_complete k hl he ht g hg s hs]
    change _ ↔ (t.step g).Elementary k (toInput (castV a) |> Linear.accumulate gs (val k))
    rw [hd.elementary_iff]
    apply Iff.of_eq
    congr 2
    have heq : a = fun i => (castV a) (Fin.cast (List.length_map ..) i) := by ext; rfl
    conv_lhs => rw [heq, Linear.accumulate_map]
  constructor
  · intro h
    obtain ⟨a,ha⟩ := (Linear.mem_columns_iff ds _ _).mp (hd.covers cs hc h)
    let b := fun i : Fin ps.length => a (E i)
    have heq : T b = x := ha
    refine ⟨b,(hp b).mpr ?_,heq⟩
    rw [heq]
    exact (Model.accumulate_vector k cs gs hc).symm ▸ h
  · rintro ⟨a,ha,hx⟩
    rw [← Model.accumulate_vector k _ _ hc]
    change (t.step g).Elementary k (Linear.accumulate gs (val k) x)
    exact hx ▸ (hp a).mp ha

/-- The full elementary basis has its level specification as soon as normal-residue reduction
satisfies its direction specification. -/
private theorem basis_spec_of_directions [CharZero k] {t : Tower R n} {g : ReducedGen (K R n)}
    {lower : Level R n}
    (hl : lower.SolveSpec k t) (he : lower.ElementaryBasisSpec k t)
    (ht : t.Admissible k) (hg : g.Admissible k t)
    {L : Level R (n+1)} (hL : L.elementaryBasis = basis t.D g lower)
    (hdirs : ∀ gs : List (K R (n+1)), let (s,ds) := directions t.D g gs
      LawfulShift g s ∧ DirectionSpec k t g gs s ds) :
    L.ElementaryBasisSpec k (t.step g) := by
  intro gs
  obtain ⟨s,ds,h⟩ : ∃ s ds, directions t.D g gs = (s,ds) := ⟨_,_,rfl⟩
  have HD := hdirs gs
  rw [h] at HD
  dsimp only at HD
  rw [hL, basis, h]
  constructor
  · exact fromDirections_sound k hl he HD.2 HD.1
  · intro cs hc
    let bs := fromDirections t.D g lower gs.length s ds
    have e := fromDirections_complete k hl he ht hg HD.2 HD.1 cs hc
    have e' (m : ℕ) (hm : m = gs.length) :
        (t.step g).Elementary k (Model.linearCombination k cs gs) ↔
          Linear.vector (RingHom.id k) m cs ∈ Submodule.span k
            ((fun z : List (K R 0) × Answer R (n+1) => Linear.vector (Model.constantHom k) m z.1) ''
              {z | z ∈ bs}) := by subst m; exact e
    refine (e' cs.length hc).trans ?_
    apply Iff.of_eq
    congr 2
    ext q
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨v.1,List.mem_map_of_mem hv,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
      exact ⟨v,hv,rfl⟩

/-- An admissible step computes every elementary combination over the model constants. -/
theorem basis_spec [CharZero k] [IsAlgClosed k] {t : Tower R n} {g : ReducedGen (K R n)}
    {lower : Level R n} (hl : lower.SolveSpec k t) (he : lower.ElementaryBasisSpec k t)
    (ht : t.Admissible k) (hg : g.Admissible k t)
    {L : Level R (n+1)} (hL : L.elementaryBasis = basis t.D g lower) :
    L.ElementaryBasisSpec k (t.step g) :=
  basis_spec_of_directions k hl he ht hg hL fun gs =>
    ⟨directions_shift t g gs, directions_spec k t g ht hg gs⟩

end SympyProofs.Calculus.Antiderivative.Elementary
