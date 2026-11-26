module

public import SympyProofs.Calculus.Antiderivative.Proof.ResiduePartition
public import SympyProofs.Calculus.Antiderivative.Extension.LogPart

/-! The modulus factors partition the set of residues. The executable degree count is the
sum of the degrees of the specialized monic greatest common divisors. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

private theorem sum_roots_prod {F A : Type} [Field F] [DecidableEq F] [AddCommMonoid A]
    (φ : F → A) (ps : List F[X]) (hs : ps.prod.Separable) :
    (ps.map fun p => ∑ c ∈ p.roots.toFinset, φ c).sum = ∑ c ∈ ps.prod.roots.toFinset, φ c := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.prod_cons] at hs ⊢
    have hz := hs.ne_zero
    have h1 : p.Separable := hs.of_dvd (dvd_mul_right ..)
    have h2 : ps.prod.Separable := hs.of_dvd (dvd_mul_left ..)
    have dis : Disjoint p.roots.toFinset ps.prod.roots.toFinset := by
      rw [Finset.disjoint_left]
      intro c hc hp
      have nd := nodup_roots hs
      rw [roots_mul hz, Multiset.nodup_add] at nd
      exact Multiset.disjoint_left.mp nd.2.2 (Multiset.mem_toFinset.mp hc)
        (Multiset.mem_toFinset.mp hp)
    rw [List.map_cons, List.sum_cons, ih h2, roots_mul hz, Multiset.toFinset_add,
      Finset.sum_union dis]

/-- The monic gcd for a single candidate residue in the model polynomial ring. -/
noncomputable def residueGcd (a d e : Poly (K R n)) (c : k) : (M k n)[X] :=
  Extension.Residue.mgcd (Step.modelPoly (val k) a - C (Model.C k n c) * Step.modelPoly (val k) e)
    (Step.modelPoly (val k) d)

/-- The output gcd at a modulus root has exactly the degree written in its bivariate piece. -/
theorem gcdPiece_value {m : Poly (K R 0)} {a d e : Poly (K R n)} (hd : d ≠ 0)
    {u : Poly (K R 0) × Step.BPoly (K R n)}
    (H : GcdPiece k m (Step.shifted a e) (Step.independent d) u)
    {c : k} (hc : (Step.modelPoly (Model.constantHom k) u.1).IsRoot c) :
    Step.specialize (Step.atRoot (val k) (Model.C k n c)) u.2 = residueGcd k a d e c ∧
      (residueGcd k a d e c).natDegree = u.2.natDegree := by
  let h := Step.atRoot (val (R := R) (n := n) k) (Model.C k n c)
  have hd' : Step.modelPoly (val k) d ≠ 0 :=
    (map_ne_zero_iff _ ((map_injective _ (val_injective (R := R) k)).comp
      Poly.equiv.injective)).mpr hd
  have dv := H.common c hc (Step.specialize h u.2)
  obtain ⟨ha,hb⟩ := dv.mp dvd_rfl
  rw [Step.specialize_shifted] at ha
  rw [Step.specialize_independent] at hb
  have hm := H.shape.resolve_left (fun hz => hd' (zero_dvd_iff.mp (by simpa [hz] using hb)))
  have hM : (Step.specialize h u.2).Monic := hm.map h
  have same : Step.specialize h u.2 = residueGcd k a d e c :=
    eq_of_monic_of_associated hM (Extension.Residue.mgcd_monic hd')
      (associated_of_dvd_dvd (Extension.Residue.dvd_mgcd ha hb) ((H.common c hc _).mpr (by
        simp only [Step.specialize_shifted, Step.specialize_independent]
        exact ⟨Extension.Residue.mgcd_dvd_left, Extension.Residue.mgcd_dvd_right⟩)))
  refine ⟨same, ?_⟩
  rw [← same]
  exact (hm.natDegree_map h).trans (Poly.natDegree_equiv _)

/-- A sum over the roots of the resultant modulus equals the sum over its output pieces. -/
theorem rawPieces_sum [DecidableEq k] [CharZero k] [IsAlgClosed k] {A : Type}
    [AddCommMonoid A] (a d e : Poly (K R n))
    (hz : residuePolynomial a d e ≠ 0) (φ : k → A) :
    ((rawPieces a d e).map fun p =>
      ∑ c ∈ (Step.modelPoly (Model.constantHom k) p.1).roots.toFinset, φ c).sum =
      ∑ c ∈ (Step.modelPoly (Model.constantHom k)
        (constantRoots (residuePolynomial a d e))).roots.toFinset, φ c := by
  let m := constantRoots (residuePolynomial a d e)
  let j := Step.modelPoly (Model.constantHom (R := R) k)
  have hs : Squarefree (j m) := constantRoots_squarefree k hz
  have sep := PerfectField.separable_iff_squarefree.mpr hs
  have deg : (j m).natDegree = m.natDegree := by simp [j, natDegree_map]
  rw [rawPieces]
  split
  · rename_i h
    have no : (j m).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      exact Nat.eq_zero_of_le_zero ((card_roots' _).trans (by simpa only [deg] using h.le))
    change (List.map _ []).sum = ∑ c ∈ (j m).roots.toFinset, φ c
    simp [no]
  · let ps := Step.gcdAtRoots K.ofConst constantRoots (d.natDegree+2) m
        (Step.shifted a e) (Step.independent d)
    have prod : (ps.map fun u => j u.1).prod = j m := by
      rw [← Step.gcdAtRoots_product K.ofConst constantRoots (d.natDegree+2) m
        (Step.shifted a e) (Step.independent d), map_list_prod, List.map_map]
      rfl
    have h := sum_roots_prod φ (ps.map fun u => j u.1) (prod ▸ sep)
    rw [prod, List.map_map] at h
    exact h

/-- Every output of the raw residue partition is a gcd piece of the constant-root modulus. -/
theorem rawPieces_spec [CharZero k] [IsAlgClosed k] (a d e : Poly (K R n))
    (hz : residuePolynomial a d e ≠ 0) {u} (hu : u ∈ rawPieces a d e) :
    GcdPiece k (constantRoots (residuePolynomial a d e)) (Step.shifted a e)
      (Step.independent d) u := by
  rw [rawPieces] at hu
  split at hu
  · simp at hu
  · rename_i hr
    refine gcdAtRoots_spec k _ (constantRoots_squarefree k hz) (Nat.pos_of_ne_zero hr) _ _ ?_ _ hu
    right
    have hd : (Step.independent d).natDegree = d.natDegree := by
      rw [← Poly.natDegree_equiv, Step.independent]
      change (Poly.equiv (d.map (algebraMap (K R n) (Poly (K R n))))).natDegree = _
      simp [natDegree_map]
    omega

/-- The degree filter removes no gcd piece of a genuine residue polynomial. Each modulus is
nonconstant and therefore has a root in the algebraically closed model constants. -/
theorem rawPieces_filter [CharZero k] [IsAlgClosed k] {a d e : Poly (K R n)}
    (hd : d ≠ 0) (hz : residuePolynomial a d e ≠ 0) :
    (rawPieces a d e).filter (fun p => p.2.natDegree != 0) = rawPieces a d e := by
  apply List.filter_eq_self.mpr
  intro u hu
  have H := rawPieces_spec k a d e hz hu
  let j := Step.modelPoly (Model.constantHom (R := R) k)
  have hp : 0 < (j u.1).natDegree := by simpa [j, natDegree_map] using H.positive
  obtain ⟨c,hc⟩ := (IsAlgClosed.splits (j u.1)).exists_eval_eq_zero
    (degree_ne_of_natDegree_ne (Nat.ne_of_gt hp))
  have hmc : (j (constantRoots (residuePolynomial a d e))).IsRoot c :=
    dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hc).trans (map_dvd j H.divides))
  have hn := (residue_roots k a d e hd c).mp hmc
  have hdeg := (gcdPiece_value k hd H hc).2
  simp only [bne_iff_ne]
  intro z
  have hm := Extension.Residue.mgcd_monic (a := Step.modelPoly (val k) a -
    C (Model.C k n c) * Step.modelPoly (val k) e) ((map_ne_zero_iff (Step.modelPoly (val k))
      ((map_injective _ (val_injective (R := R) k)).comp Poly.equiv.injective)).mpr hd)
  have hone : residueGcd k a d e c = 1 := eq_one_of_monic_natDegree_zero hm (hdeg.trans z)
  obtain ⟨x,y,hxy⟩ := Extension.Residue.mgcd_bezout
    (Step.modelPoly (val k) a - C (Model.C k n c) * Step.modelPoly (val k) e)
    (Step.modelPoly (val k) d)
  exact hn ⟨y,x, (add_comm _ _).trans (hxy.trans hone)⟩

/-- The executable degree count equals the sum of the degrees of the actual residue gcds. -/
theorem accounted_spec [DecidableEq k] [CharZero k] [IsAlgClosed k] {a d e : Poly (K R n)}
    (hd : d ≠ 0) (hz : residuePolynomial a d e ≠ 0) :
    ((rawPieces a d e).map fun p => p.1.natDegree * p.2.natDegree).sum =
      ∑ c ∈ (Step.modelPoly (Model.constantHom k)
        (constantRoots (residuePolynomial a d e))).roots.toFinset,
          (residueGcd k a d e c).natDegree := by
  rw [← rawPieces_sum k a d e hz]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  have H := rawPieces_spec k a d e hz hu
  let m := Step.modelPoly (Model.constantHom (R := R) k) u.1
  have sq : Squarefree m := Squarefree.squarefree_of_dvd (map_dvd _ H.divides)
    (constantRoots_squarefree k hz)
  have hcard : m.roots.toFinset.card = u.1.natDegree := by
    rw [Multiset.toFinset_card_of_nodup
      (nodup_roots (PerfectField.separable_iff_squarefree.mpr sq)),
      ← (IsAlgClosed.splits m).natDegree_eq_card_roots]
    simp [m, natDegree_map]
  change _ = ∑ c ∈ m.roots.toFinset, _
  rw [Finset.sum_congr rfl (fun c hc => (gcdPiece_value k hd H
    ((mem_roots sq.ne_zero).mp (Multiset.mem_toFinset.mp hc))).2), Finset.sum_const, hcard,
    smul_eq_mul]

end SympyProofs.Calculus.Antiderivative.Residue
