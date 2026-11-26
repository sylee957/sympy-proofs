module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.SharedParts

/-! The computed normal-residue directions account for all elementary combinations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

private theorem model_mix (v : List (K R 0)) (ps : List (Poly (K R n))) :
    Step.modelPoly (val k) (Solve.mix v ps) =
      Model.polynomialCombination k (v.map (Model.constantHom k)) ps := by
  induction v generalizing ps with
  | nil => simp [Solve.mix, Model.polynomialCombination]
  | cons c cs ih =>
    cases ps with
    | nil => simp [Solve.mix, Model.polynomialCombination]
    | cons p ps =>
      simp only [Solve.mix, List.zipWith_cons_cons, List.sum_cons, map_add, map_mul,
        Step.modelPoly_apply, Poly.equiv_C, Polynomial.map_C, List.map_cons,
        Model.polynomialCombination, Model.C_constantHom] at ih ⊢
      rw [ih]

private theorem model_join (a b : Poly (K R n)) :
    (Model.stepEquiv k n).symm
      (algebraMap (M k n)[X] _ (Step.modelPoly (val k) a) /
        algebraMap (M k n)[X] _ (Step.modelPoly (val k) b)) = val k (K.join a b) := by
  apply (Model.stepEquiv k n).injective
  simp [K.join, val_joinPoly]

private theorem vector_map {F : Type} [Field F] (f : F →+* k) (m : ℕ) (v : List F) :
    Linear.vector (RingHom.id k) m (v.map f) = Linear.vector f m v := by
  ext i
  simp [Linear.vector, List.getD_eq_getElem?_getD]
  cases v[i.val]? <;> simp

variable [CharZero k] [IsAlgClosed k]
variable {t : Tower R n} {g : ReducedGen (K R n)} {gs : List (K R (n+1))}
variable {j : ℕ} {s : Poly (K R n)} {ps : List (Parts R n)}

private theorem direction_of_kernel (ht : t.Admissible k) (h : SharedParts k t g gs j s ps)
    (v : List (K R 0)) (hv : v ∈ Linear.kernel
      (residueRows t.D (g.velocity t.D) s (ps.map Parts.proper))
      gs.length) : ∃ d, direction t.D (g.velocity t.D) s j ps v = some d ∧ d.coords = v ∧
        d.answer.Regular k ∧ d.answer.deriv k (t.step g) +
          laurentValue k j (Solve.modelPoly k d.rest) =
          Model.linearCombination k (v.map (Model.constantHom k)) gs := by
  let m := Solve.mix v (ps.map Parts.proper)
  let e := Step.polyDer t.D (g.velocity t.D) s
  let cs := v.map (Model.constantHom k)
  have hm : Step.modelPoly (val k) m = Model.polynomialCombination k cs (ps.map Parts.proper) :=
    model_mix k _ _
  have hinput : Residue.Input k t g m s := ⟨h.squarefree,h.normal,by
    rw [hm]
    apply combination_proper k _ h.squarefree.ne_zero
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact h.proper p hp⟩
  have hrows : ∀ row ∈ residueRows t.D (g.velocity t.D) s (ps.map Parts.proper),
      Model.rowHolds k row cs := by
    intro row hr
    rw [Model.rowHolds_iff_functional]
    dsimp only [cs]
    rw [List.length_map, Linear.length_of_mem_kernel _ _ _ hv, vector_map]
    exact Linear.kernel_sound (Model.constantHom k) _ _ hv hr
  have hres := (residueRows_spec k t g ht s h.squarefree h.normal cs (ps.map Parts.proper)).mp hrows
  rw [← hm] at hres
  have success := Residue.logPart_of_residues k t g hinput hres
  cases hl : Residue.logPart m s e ((g.velocity t.D).coeff 1) with
  | none => exact (success hl).elim
  | some out =>
    obtain ⟨logs,corr⟩ := out
    obtain ⟨hreg,hlogs⟩ := Residue.logPart_sound k t g hinput hl
    let l := Solve.mix v (ps.map Parts.laurent)
    let exactPart := Level.combine v (ps.map Parts.exactPart)
    let d : Direction R n := ⟨v,⟨exactPart,logs⟩,l + Poly.monomial j corr⟩
    refine ⟨d, ?_, rfl, hreg, ?_⟩
    · dsimp only [m,e] at hl
      simp [direction, hl, d, l, exactPart]
    · rw [h.identity, ← hm, model_join, hlogs]
      change (t.step g).modelD k (val k (Level.combine v _)) + _ +
        laurentValue k j (Solve.modelPoly k (l + Poly.monomial j corr)) = _
      rw [Level.val_combine]
      change _ + laurentValue k j (Step.modelPoly (val k) (l + Poly.monomial j corr)) = _
      rw [map_add, laurentValue_add]
      have hl' := model_mix k v (ps.map Parts.laurent)
      change Step.modelPoly (val k) l = _ at hl'
      rw [hl']
      simp only [Step.modelPoly_apply, Poly.equiv_monomial, map_monomial,
        laurentValue_monomial, val_lift]
      abel

private theorem rows_of_elementary (ht : t.Admissible k) (h : SharedParts k t g gs j s ps)
    (cs : List k) (he : (t.step g).Elementary k (Model.linearCombination k cs gs)) :
    ∀ row ∈ residueRows t.D (g.velocity t.D) s (ps.map Parts.proper), Model.rowHolds k row cs := by
  let P := Model.polynomialCombination k cs (ps.map Parts.proper)
  let Q := Model.polynomialCombination k cs (ps.map Parts.laurent)
  let D := Step.modelPoly (val k) s
  let L := algebraMap (M k n)[X] (RatFunc (M k n)) Q / RatFunc.X ^ j
  apply (residueRows_spec k t g ht s h.squarefree h.normal cs _).mpr
  apply Residue.model_residues_necessary k t g P D h.squarefree h.normal L
  · intro q hq hd
    refine ⟨Q,X^j,fun hqj => hq.not_isUnit (h.coprime.isUnit_of_dvd' hqj hd), ?_⟩
    simp [L, pow_ne_zero j (RatFunc.X_ne_zero : (RatFunc.X : RatFunc (M k n)) ≠ 0)]
  · let w := (t.step g).modelD k (Model.linearCombination k cs (ps.map Parts.exactPart))
    have hx : (t.step g).Elementary k w :=
      ⟨Model.linearCombination k cs (ps.map Parts.exactPart), [], by simp [w]⟩
    convert he.sub k hx using 1
    rw [h.identity, map_add]
    change _ + _ = w + _ + (Model.stepEquiv k n).symm L - w
    abel

private theorem kernel_directions (ht : t.Admissible k) (h : SharedParts k t g gs j s ps) :
    let rows := residueRows t.D (g.velocity t.D) s (ps.map Parts.proper)
    let ds := (Linear.kernel rows gs.length).filterMap (direction t.D (g.velocity t.D) s j ps)
    DirectionSpec k t g gs j ds := by
  let rows := residueRows t.D (g.velocity t.D) s (ps.map Parts.proper)
  let vs := Linear.kernel rows gs.length
  let ds := vs.filterMap (direction t.D (g.velocity t.D) s j ps)
  have hout (d : Direction R n) (hd : d ∈ ds) : d.coords ∈ vs ∧ d.answer.Regular k ∧
      d.answer.deriv k (t.step g) + laurentValue k j (Solve.modelPoly k d.rest) =
        Model.linearCombination k (d.coords.map (Model.constantHom k)) gs := by
    obtain ⟨v,hv,hdir⟩ := List.mem_filterMap.mp hd
    obtain ⟨d',hd',he,hreg,hs⟩ := direction_of_kernel k ht h v hv
    obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hdir)
    exact ⟨he ▸ hv, hreg, he ▸ hs⟩
  refine ⟨fun d hd => Linear.length_of_mem_kernel _ _ _ (hout d hd).1,
    fun d hd => (hout d hd).2.1, fun d hd => (hout d hd).2.2, ?_⟩
  intro cs hlen hE
  have hh := rows_of_elementary k ht h cs hE
  have hspan : Linear.vector (RingHom.id k) gs.length cs ∈
      Linear.generated (Model.constantHom k) rows gs.length := by
    apply (Linear.generated_iff _ _ _ _).mpr
    intro r hr
    have hrow := (Model.rowHolds_iff_functional k r cs).mp (hh r hr)
    rwa [hlen] at hrow
  apply Submodule.span_mono _ hspan
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨d,hd,he,_,_⟩ := direction_of_kernel k ht h v hv
  exact ⟨d,List.mem_filterMap.mpr ⟨v,hv,hd⟩,congrArg _ he⟩

/-- Every admissible primitive or exponential step supplies precisely enough normal-residue
directions to decide elementary integration of every model-linear combination. -/
theorem directions_spec (t : Tower R n) (g : ReducedGen (K R n)) (ht : t.Admissible k)
    (hg : g.Admissible k t) (gs : List (K R (n+1))) :
    DirectionSpec k t g gs (directions t.D g gs).1 (directions t.D g gs).2 :=
  kernel_directions k ht (sharedParts_spec k t g hg gs)

theorem directions_shift (t : Tower R n) (g : ReducedGen (K R n)) (gs : List (K R (n+1))) :
    LawfulShift g (directions t.D g gs).1 := by
  cases g <;> simp [directions, LawfulShift, poleOrder]

end SympyProofs.Calculus.Antiderivative.Elementary
