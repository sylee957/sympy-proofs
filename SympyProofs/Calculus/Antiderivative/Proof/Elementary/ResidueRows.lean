module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.AlgebraicConstants
public import SympyProofs.Calculus.Antiderivative.Proof.ElementaryParts
public import SympyProofs.Calculus.Antiderivative.Proof.Step.ParametricResidues
public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants

/-! The residue equations characterize precisely the directions with constant residues. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial
open scoped Differential

/-- Sum products of scalar weights with the corresponding field elements. -/
private def weighted {k E : Type} [Field k] [Field E] (f : k →+* E) :
    List k → List E → E
  | c :: cs, x :: xs => f c * x + weighted f cs xs
  | _, _ => 0

private theorem weighted_deriv {k E : Type} [Field k] [Field E] [Differential E]
    (j : k →+* E) (hj : ∀ c, (j c)′ = 0) (cs : List k) (ys : List E) :
    (weighted j cs ys)′ = weighted j cs (ys.map Differential.deriv) := by
  induction cs generalizing ys with
  | nil => simp [weighted]
  | cons c cs ih => cases ys <;> simp [weighted, ih, Derivation.leibniz, hj, smul_eq_mul]

private theorem weighted_div {k E : Type} [Field k] [Field E] (j : k →+* E)
    (cs : List k) (ys : List E) (b : E) :
    weighted j cs ys / b = weighted j cs (ys.map (· / b)) := by
  induction cs generalizing ys with
  | nil => simp [weighted]
  | cons c cs ih => cases ys <;> simp [weighted, ih, add_div, mul_div_assoc]

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

private theorem map_combination {E : Type} [Field E] (f : (M k n)[X] →+* E)
    (cs : List k) (as : List (Poly (K R n))) :
    f (Model.polynomialCombination k cs as) =
      weighted ((f.comp C).comp (Model.C k n)) cs
        (as.map fun a => f (Step.modelPoly (val k) a)) := by
  induction cs generalizing as with
  | nil => simp [Model.polynomialCombination, weighted]
  | cons c cs ih => cases as <;> simp [Model.polynomialCombination, weighted, ih]

private theorem reflect_coprime (p q : Poly (K R n))
    (h : IsCoprime (Step.modelPoly (val k) p) (Step.modelPoly (val k) q)) :
    IsCoprime p q := by
  have hc : IsCoprime (Poly.equiv p) (Poly.equiv q) := (isCoprime_map (val k)).mp h
  exact (by simpa using hc.map Poly.equiv.symm.toRingHom)

private theorem source_coprime (t : Tower R n) (g : ReducedGen (K R n)) (s : Poly (K R n))
    (hs : Squarefree (Step.modelPoly (val k) s))
    (hn : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) s →
      ¬ p ∣ t.polyDerModel k g p) [CharZero k] :
    IsCoprime s.derivative s ∧ IsCoprime (Step.polyDer t.D (g.velocity t.D) s) s := by
  constructor
  · apply reflect_coprime k
    have h := (PerfectField.separable_iff_squarefree.mpr hs).symm
    simpa [derivative_map] using h
  · apply reflect_coprime k
    rw [Tower.modelPoly_polyDer]
    apply IsCoprime.symm
    exact isCoprime_of_prime_dvd (fun bad => hs.ne_zero bad.1) fun p hp hd =>
      Extension.Residue.not_dvd_deriv _ hs hp hd (hn p hp hd)

variable [CharZero k] [IsAlgClosed k]

private theorem prime_residue (t : Tower R n) (g : ReducedGen (K R n)) (ht : t.Admissible k)
    (d : Poly (K R n)) (hs : Squarefree (Step.modelPoly (val k) d))
    (hn : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d →
      ¬ p ∣ t.polyDerModel k g p)
    (p : (M k n)[X]) (hm : p.Monic) (hi : Irreducible p) (hp : p ∣ Step.modelPoly (val k) d)
    (cs : List k) (as : List (Poly (K R n))) :
    p ∣ Model.polynomialCombination k cs (Step.residueDerivatives t.D (g.velocity t.D) d as) ↔
      ∃ c : k, p ∣ Model.polynomialCombination k cs as -
        C (Model.C k n c) * t.polyDerModel k g (Step.modelPoly (val k) d) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let _ : Differential (K R n) := ⟨K.derivation t.gens⟩
  let _ : Fact p.Monic := ⟨hm⟩
  let _ : Fact (Irreducible p) := ⟨hi⟩
  let E := AdjoinRoot p
  let u : (M k n)[X] →+* E := AdjoinRoot.mk p
  let j := (algebraMap (M k n) E).comp (Model.C k n)
  let ev := u.comp (Step.modelPoly (val (R := R) (n := n) k))
  let fld := (algebraMap (M k n) E).comp (val (R := R) (n := n) k)
  let _ : Algebra (K R n) E := fld.toAlgebra
  let _ : DifferentialAlgebra (K R n) E := ⟨fun a => by
    change (algebraMap (M k n) E (val k a))′ = algebraMap (M k n) E (val k (t.D a))
    rw [DifferentialAlgebra.deriv_algebraMap]
    exact congrArg _ (t.val_D k a).symm⟩
  let e := Step.polyDer t.D (g.velocity t.D) d
  let r := weighted j cs (as.map ev) / ev e
  have he : ev e ≠ 0 := by
    change AdjoinRoot.mk p (Step.modelPoly (val k) e) ≠ 0
    rw [ne_eq, AdjoinRoot.mk_eq_zero, show e = _ from rfl, Tower.modelPoly_polyDer]
    exact Extension.Residue.not_dvd_deriv _ hs hi.prime hp (hn _ hi.prime hp)
  have hroot : Step.rootEval (F := K R n) (AdjoinRoot.root p) = ev := by
    ext a
    change aeval (R := K R n) (AdjoinRoot.root p) (Poly.equiv a) =
      AdjoinRoot.mk p ((Poly.equiv a).map (val k))
    rw [← AdjoinRoot.aeval_eq, aeval_def, aeval_def, eval₂_map]
    rfl
  obtain ⟨h1,h2⟩ := source_coprime k t g d hs hn
  have hdz : Step.rootEval (F := K R n) (AdjoinRoot.root p) d = 0 := by
    rw [hroot]
    exact AdjoinRoot.mk_eq_zero.mpr hp
  have hlist := Step.residueDerivatives_spec (AdjoinRoot.root p) (g.velocity t.D) d as hdz h1 h2
  rw [hroot] at hlist
  change (Step.residueDerivatives t.D (g.velocity t.D) d as).map ev =
    as.map (fun a => (ev a / ev e)′) at hlist
  have hj (c : k) : (j c)′ = 0 := by
    change (algebraMap (M k n) E (Model.C k n c))′ = 0
    rw [DifferentialAlgebra.deriv_algebraMap]
    exact (congrArg _ (t.modelD_C k c)).trans (map_zero _)
  have hder : u (Model.polynomialCombination k cs
      (Step.residueDerivatives t.D (g.velocity t.D) d as)) = r′ := by
    rw [map_combination]
    change weighted j cs ((Step.residueDerivatives t.D (g.velocity t.D) d as).map ev) = _
    rw [hlist]
    dsimp only [r]
    rw [weighted_div, weighted_deriv _ hj]
    simp [List.map_map, Function.comp_def]
  have hconst (y : M k n) : y′ = 0 ↔ y ∈ (Model.C k n).range := by
    change t.modelD k y = 0 ↔ _
    rw [ht y]
    simp only [RingHom.mem_range, eq_comm]
  let _ : Algebra.IsIntegral (M k n) E := AdjoinRoot.isIntegral_of_monic hm
  have hiff : r′ = 0 ↔ r ∈ j.range :=
    algebraic_constant_iff (Model.C k n) hconst r (Algebra.IsIntegral.isIntegral r)
  rw [← AdjoinRoot.mk_eq_zero]
  change u _ = 0 ↔ _
  rw [hder]
  rw [hiff]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c, AdjoinRoot.mk_eq_zero.mp ?_⟩
    change u (_ - _) = 0
    rw [map_sub, map_mul, ← Tower.modelPoly_polyDer, map_combination]
    change weighted j cs (as.map ev) - j c * ev e = 0
    exact sub_eq_zero.mpr ((div_eq_iff he).mp hc.symm)
  · rintro ⟨c,hc⟩
    have hzero := AdjoinRoot.mk_eq_zero.mpr hc
    change u (_ - _) = 0 at hzero
    rw [map_sub, map_mul, ← Tower.modelPoly_polyDer, map_combination] at hzero
    refine ⟨c, ((div_eq_iff he).mpr (sub_eq_zero.mp hzero)).symm⟩

omit [CharZero k] [IsAlgClosed k] in
theorem combination_proper (B : (M k n)[X]) (hB : B ≠ 0) (cs : List k)
    (as : List (Poly (K R n))) (h : ∀ a ∈ as, (Step.modelPoly (val k) a).degree < B.degree) :
    (Model.polynomialCombination k cs as).degree < B.degree := by
  have hz : (0 : (M k n)[X]).degree < B.degree := by
    rw [degree_zero, degree_eq_natDegree hB]
    exact WithBot.bot_lt_coe _
  induction cs generalizing as with
  | nil => exact hz
  | cons c cs ih =>
    cases as with
    | nil => exact hz
    | cons a as =>
      apply (degree_add_le _ _).trans_lt (max_lt _ _)
      · by_cases hc : c = 0
        · simpa [hc] using hz
        · rw [degree_C_mul ((map_ne_zero_iff _ (Model.C k n).injective).mpr hc)]
          exact h a (by simp)
      · exact ih as fun p hp => h p (List.mem_cons_of_mem _ hp)

omit [CharZero k] [IsAlgClosed k] in
private theorem derivative_combo_proper (t : Tower R n) (g : ReducedGen (K R n))
    (d : Poly (K R n))
    (hd : Step.modelPoly (val k) d ≠ 0) (cs : List k) (as : List (Poly (K R n))) :
    (Model.polynomialCombination k cs (Step.residueDerivatives t.D (g.velocity t.D) d as)).degree <
      (Step.modelPoly (val k) d).degree := by
  apply combination_proper k _ hd
  intro a ha
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
  simp only [Step.modelPoly_apply, Poly.equiv_mod, degree_map]
  exact degree_mod_lt _ ((Polynomial.map_ne_zero_iff (val (R := R) (n := n) k).injective).mp hd)

/-- The computed linear equations vanish exactly when each normal prime has a residue in the
model's constant field. The coefficients of the combination may be arbitrary model constants. -/
theorem residueRows_spec (t : Tower R n) (g : ReducedGen (K R n)) (ht : t.Admissible k)
    (d : Poly (K R n)) (hs : Squarefree (Step.modelPoly (val k) d))
    (hn : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d →
      ¬ p ∣ t.polyDerModel k g p)
    (cs : List k) (as : List (Poly (K R n))) :
    (∀ row ∈ residueRows t.D (g.velocity t.D) d as, Model.rowHolds k row cs) ↔
      ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d →
        ∃ c : k, p ∣ Model.polynomialCombination k cs as -
          C (Model.C k n c) * t.polyDerModel k g (Step.modelPoly (val k) d) := by
  classical
  let vs := Step.residueDerivatives t.D (g.velocity t.D) d as
  let P := Model.polynomialCombination k cs vs
  let D := Step.modelPoly (val k) d
  have hdeg : P.degree < D.degree := derivative_combo_proper k t g d hs.ne_zero cs as
  have hz : (∀ row ∈ residueRows t.D (g.velocity t.D) d as, Model.rowHolds k row cs) ↔ P = 0 := by
    by_cases hd : d.natDegree = 0
    · have hdd : D.degree = 0 := by
        rw [degree_eq_natDegree hs.ne_zero]
        simp [hd]
      rw [hdd] at hdeg
      simp [residueRows, hd, show P = 0 by simpa using hdeg]
    · change (∀ row ∈ (if d.natDegree = 0 then [] else (coefficientSlices vs).flatMap rowsOf),
        Model.rowHolds k row cs) ↔ Model.polynomialCombination k cs vs = 0
      simp only [hd, ↓reduceIte, List.mem_flatMap, forall_exists_index, and_imp]
      rw [← Model.polynomialCombination_eq_zero]
      constructor
      · exact fun h u hu => (rowsOf_spec k u cs).mp fun r hr => h r u hu hr
      · exact fun h r u hu hr => (rowsOf_spec k u cs).mpr (h u hu) r hr
  rw [hz]
  have local_iff (p : (M k n)[X]) (hp : Prime p) (hpd : p ∣ D) :
      p ∣ P ↔ ∃ c : k, p ∣ Model.polynomialCombination k cs as -
        C (Model.C k n c) * t.polyDerModel k g D := by
    have h := prime_residue k t g ht d hs hn (normalize p) (monic_normalize hp.ne_zero)
      ((associated_normalize p).irreducible_iff.mp hp.irreducible) (by simpa [D] using hpd) cs as
    simpa [P, vs, D] using h
  constructor
  · exact fun h p hp hpd => (local_iff p hp hpd).mp (h ▸ dvd_zero _)
  · exact fun h => eq_zero_of_dvd_of_degree_lt
      (Extension.Residue.dvd_of_squarefree hs fun p hp hpd =>
        (local_iff p hp hpd).mpr (h p hp hpd)) hdeg

end SympyProofs.Calculus.Antiderivative.Elementary
