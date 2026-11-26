module

public import SympyProofs.Calculus.Antiderivative.Proof.Row

/-! Correctness of integration, parametric solving, and the logarithmic relation rows over
the constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- Every model fraction in zero variables is a coefficient of the model. -/
theorem Model.C_surjective_zero : Function.Surjective (Model.C k 0) := by
  intro z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 0) k) z
  let e := MvPolynomial.isEmptyRingEquiv k (Fin 0)
  refine ⟨e a / e b, ?_⟩
  have h (p : MvPolynomial (Fin 0) k) : MvPolynomial.C (e p) = p :=
    (MvPolynomial.isEmptyRingEquiv_symm_apply k (Fin 0) (e p)).symm.trans (e.symm_apply_apply p)
  rw [map_div₀]
  change algebraMap (MvPolynomial (Fin 0) k) (M k 0) (MvPolynomial.C (e a)) /
    algebraMap (MvPolynomial (Fin 0) k) (M k 0) (MvPolynomial.C (e b)) = _
  rw [h, h]

/-- The model derivative vanishes throughout a tower of height zero. -/
@[simp] theorem Tower.modelD_base (x : M k 0) : (base : Tower R 0).modelD k x = 0 := by
  simp [modelD, gens, Model.derivation_apply, Model.der, Model.weightedPartials]

/-- At height zero exactly zero has a Liouville-form integral. -/
theorem Tower.elementary_base (x : M k 0) :
    (base : Tower R 0).Elementary k x ↔ x = 0 := by
  constructor
  · rintro ⟨y, logs, h⟩
    simpa using h
  · rintro rfl
    exact ⟨0, [], by simp⟩

variable [IntegerRelations (K R 0)]

/-- The base integration decision is sound and complete over the model constants. -/
theorem baseLevel_integrate_spec : (baseLevel R).IntegrateSpec k (.base : Tower R 0) := by
  intro f
  by_cases hf : f = 0
  · subst f
    simp [baseLevel, Answer.Regular, Answer.deriv]
  · simp [baseLevel, hf, Tower.elementary_base]

omit [IntegerRelations (K R 0)] in
private theorem base_row (cs : List k) (gs : List (K R 0)) (h : cs.length = gs.length)
    (d : k) (f : K R 0) :
    Model.linearCombination k (cs ++ [d]) (gs.map (- ·) ++ [f]) =
      Model.C k 0 d * val k f - Model.linearCombination k cs gs := by
  induction cs generalizing gs with
  | nil =>
    cases gs with
    | nil => simp [Model.linearCombination]
    | cons => simp at h
  | cons c cs ih =>
    cases gs with
    | nil => simp at h
    | cons g gs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.cons_append, List.map_cons, Model.linearCombination, map_neg, ih gs h]
      ring

/-- The single homogeneous row describes all solutions of the base parametric equation. -/
theorem baseLevel_solve_spec : (baseLevel R).SolveSpec k (.base : Tower R 0) := by
  intro f gs y cs hc
  change (Tower.base.modelD k y + val k f * y = Model.linearCombination k cs gs) ↔
    ∃ d : List k, d.length = 1 ∧ y = Model.linearCombination k d [1] ∧
      ∀ r ∈ [gs.map (- ·) ++ [f]], Model.rowHolds k r (cs ++ d)
  rw [Tower.modelD_base, zero_add]
  constructor
  · intro he
    obtain ⟨a, rfl⟩ := Model.C_surjective_zero k y
    refine ⟨[a], rfl, by simp [Model.linearCombination], ?_⟩
    intro r hr
    rw [List.mem_singleton.mp hr, Model.rowHolds, base_row k _ _ hc, mul_comm, he, sub_self]
  · rintro ⟨d, hd, rfl, hr⟩
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hd
    have h := hr _ (List.mem_singleton_self _)
    rw [Model.rowHolds, base_row k _ _ hc, sub_eq_zero, mul_comm] at h
    simpa [Model.linearCombination] using h

/-- At height zero the elementary combinations form the scalar extension of the computed kernel. -/
theorem baseLevel_elementaryBasis_spec :
    (baseLevel R).ElementaryBasisSpec k (.base : Tower R 0) := by
  intro gs
  constructor
  · rintro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    have hl := Linear.length_of_mem_kernel [gs] gs.length r hr
    refine ⟨hl, by simp [Answer.Regular], ?_⟩
    simp only [Answer.deriv, Tower.modelD_base, List.map_nil, List.sum_nil, add_zero]
    apply Eq.symm
    change Model.rowHolds k gs _
    rw [Model.rowHolds_iff_functional, List.length_map, hl]
    have hv : Linear.vector (RingHom.id k) gs.length (r.map (Model.constantHom k)) =
        Linear.vector (Model.constantHom k) gs.length r := by
      ext i
      simp only [Linear.vector, RingHom.id_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases r[(i : ℕ)]? <;> simp
    rw [hv]
    exact Linear.kernel_sound _ _ _ hr (List.mem_singleton_self gs)
  · intro cs h
    rw [Tower.elementary_base]
    change Model.rowHolds k gs cs ↔ _
    rw [Model.rowHolds_iff_functional]
    simp only [baseLevel, List.map_map, Function.comp_def]
    rw [show (fun x : List (K R 0) => x) = id from rfl, List.map_id]
    rw [← h]
    change _ ↔ Linear.vector (RingHom.id k) cs.length cs ∈
      Linear.generated (Model.constantHom k) [gs] cs.length
    simp only [Linear.generated_iff, List.mem_singleton, forall_eq]

end SympyProofs.Calculus.Antiderivative
