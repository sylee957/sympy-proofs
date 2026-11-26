module

public import SympyProofs.Calculus.Antiderivative.Proof.Residue
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect

/-! The modulus gcd over the constants agrees with the coefficient-field gcd on a squarefree
modulus. This is what permits Euclidean division to split only by polynomials in the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Coefficientwise scalar inclusion commutes with both interpretations of a constant polynomial. -/
theorem modelPoly_ofConst (m : Poly (K R 0)) :
    Step.modelPoly (val k) (m.map (K.ofConst (n := n))) =
      (Step.modelPoly (Model.constantHom k) m).map (Model.C k n) := by
  simp only [Step.modelPoly_apply, Poly.equiv_map, Polynomial.map_map]
  congr 1
  ext c
  exact (Model.C_constantHom k c).symm

private theorem equal_monic_divisors {G : Type} [Field G] {m p q : G[X]}
    (hs : m.Splits) (hm : m.Separable) (dp : p ∣ m) (dq : q ∣ m)
    (mp : p.Monic) (mq : q.Monic) (h : ∀ x, p.IsRoot x ↔ q.IsRoot x) : p = q := by
  have hp := hs.of_dvd hm.ne_zero dp
  have hq := hs.of_dvd hm.ne_zero dq
  have hr : p.roots = q.roots := (Multiset.Nodup.ext (nodup_roots (hm.of_dvd dp))
    (nodup_roots (hm.of_dvd dq))).mpr
      (fun x => by rw [mem_roots mp.ne_zero, mem_roots mq.ne_zero, h])
  rw [hp.eq_prod_roots_of_monic mp, hq.eq_prod_roots_of_monic mq, hr]

private theorem model_gcd_monic {F G : Type} [Field F] [DecidableEq F] [Field G]
    (j : F →+* G) {a : Poly F} (ha : a ≠ 0) (b : Poly F) : (Step.modelPoly j (gcd a b)).Monic :=
  (show (Poly.equiv (gcd a b)).Monic by simp [Monic, ha]).map j

private theorem model_gcd_root {F G : Type} [Field F] [DecidableEq F] [Field G]
    (j : F →+* G) (a b : Poly F) (z : G) :
    (Step.modelPoly j (gcd a b)).IsRoot z ↔
      (Step.modelPoly j a).IsRoot z ∧ (Step.modelPoly j b).IsRoot z :=
  Step.map_gcd_eq_zero_iff (Step.atRoot j z) a b

/-- Over an algebraically closed constant extension, the divisor on which the leading
coefficient vanishes is precisely the ordinary computable gcd in the tower field. -/
theorem commonFactor_ofConst [CharZero k] [IsAlgClosed k] {m : Poly (K R 0)}
    (hm : Squarefree (Step.modelPoly (Model.constantHom k) m)) (l : Poly (K R n)) :
    (gcd m (constantRoots l)).map K.ofConst = gcd (m.map K.ofConst) l := by
  let j := Model.constantHom (R := R) k
  let v := val (R := R) (n := n) k
  let c := Model.C k n
  let M₀ := Step.modelPoly j m
  have hm' : m ≠ 0 := by rintro rfl; simp at hm
  have Mz : M₀ ≠ 0 := hm.ne_zero
  have hF : m.map (K.ofConst (n := n)) ≠ 0 := by
    intro hz
    have h := modelPoly_ofConst (n := n) k m
    rw [hz, map_zero] at h
    exact ((Polynomial.map_ne_zero_iff c.injective).mpr Mz) h.symm
  let g := gcd m (constantRoots l)
  have dg : Step.modelPoly j g ∣ M₀ := map_dvd (Step.modelPoly j) (gcd_dvd_left _ _)
  have dq := map_dvd (Step.modelPoly v) (gcd_dvd_left (m.map K.ofConst) l)
  rw [modelPoly_ofConst] at dq
  apply (Polynomial.map_injective _ (val_injective (n := n) k)).comp Poly.equiv.injective
  change Step.modelPoly v (g.map K.ofConst) = Step.modelPoly v (gcd (m.map K.ofConst) l)
  rw [modelPoly_ofConst]
  have hs := IsAlgClosed.splits M₀
  apply equal_monic_divisors (hs.map c)
    ((separable_map c).mpr (PerfectField.separable_iff_squarefree.mpr hm))
    (by simpa using map_dvd (Polynomial.mapRingHom c) dg) dq
    ((model_gcd_monic j hm' _).map c) (model_gcd_monic v hF _)
  intro x
  rw [model_gcd_root]
  by_cases hx : (M₀.map c).IsRoot x
  · obtain ⟨u, rfl⟩ := hs.mem_range_of_isRoot Mz hx
    have hroot (p : k[X]) : (p.map c).IsRoot (c u) ↔ p.IsRoot u := by
      rw [IsRoot.def, eval_map_apply, map_eq_zero_iff c c.injective]
      rfl
    rw [modelPoly_ofConst, hroot, hroot, model_gcd_root, constantRoots_spec]
  · have H (hr : ((Step.modelPoly j g).map c).IsRoot x) : (M₀.map c).IsRoot x :=
      dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hr).trans (by
        simpa using map_dvd (Polynomial.mapRingHom c) dg))
    rw [modelPoly_ofConst]
    exact ⟨fun h => (hx (H h)).elim, fun h => (hx h.1).elim⟩

/-- Specializing an embedded constant polynomial gives its scalar value in the model. -/
theorem atRoot_ofConst (m : Poly (K R 0)) (c : k) :
    Step.atRoot (val (n := n) k) (Model.C k n c) (m.map K.ofConst) =
      Model.C k n (Step.atRoot (Model.constantHom k) c m) := by
  change (Step.modelPoly (val k) (m.map K.ofConst)).eval _ = _
  rw [modelPoly_ofConst, eval_map_apply]
  rfl

/-- The two branches of a nontrivial leading-coefficient split both have smaller positive
degree. The leading coefficient has already been reduced modulo the input modulus. -/
theorem split_degrees [CharZero k] [IsAlgClosed k] {m : Poly (K R 0)} {l : Poly (K R n)}
    (hm : Squarefree (Step.modelPoly (Model.constantHom k) m))
    (hl : l ≠ 0) (hd : l.natDegree < m.natDegree)
    (hg : 0 < (gcd m (constantRoots l)).natDegree) :
    let g := gcd m (constantRoots l)
    g.natDegree < m.natDegree ∧ 0 < (m / g).natDegree ∧ (m / g).natDegree < m.natDegree := by
  let g := gcd m (constantRoots l)
  have hg0 : g ≠ 0 := by rintro h; change 0 < g.natDegree at hg; simp [h] at hg
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have he : g * (m / g) = m := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left ..)
  have hq0 : m / g ≠ 0 := fun h => hm0 (by rw [← he, h, mul_zero])
  have hf : g.map K.ofConst ∣ l := (commonFactor_ofConst k hm l).symm ▸ gcd_dvd_right _ _
  have h := natDegree_le_of_dvd (map_dvd Poly.equiv hf)
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr hl)
  simp only [Poly.equiv_map, natDegree_map, Poly.natDegree_equiv] at h
  have hs := congrArg (fun z => (Poly.equiv z).natDegree) he
  rw [map_mul, natDegree_mul ((map_ne_zero_iff _ Poly.equiv.injective).mpr hg0)
    ((map_ne_zero_iff _ Poly.equiv.injective).mpr hq0)] at hs
  simp only [Poly.natDegree_equiv] at hs
  change 0 < g.natDegree at hg
  dsimp only
  change g.natDegree < _ ∧ 0 < (m / g).natDegree ∧ (m / g).natDegree < _
  omega

private theorem scalar_gcd_one [CharZero k] [IsAlgClosed k] {m : Poly (K R 0)}
    (hm : Squarefree (Step.modelPoly (Model.constantHom k) m)) {l : Poly (K R n)}
    (hd : (gcd m (constantRoots l)).natDegree = 0) : gcd l (m.map K.ofConst) = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  let g := gcd m (constantRoots l)
  have he : g = 1 := by
    apply Poly.equiv.injective
    have d₀ : (Poly.equiv g).natDegree = 0 := by simpa using hd
    have hc : (Poly.equiv g).coeff 0 = 1 := by
      simpa only [d₀, Poly.leadingCoeff_equiv, g, Poly.leadingCoeff_gcd_of_left_ne_zero hm0]
        using coeff_natDegree (p := Poly.equiv g)
    rw [eq_C_of_natDegree_eq_zero d₀, hc, map_one, map_one]
  rw [gcd_comm, ← commonFactor_ofConst k hm l, show gcd m (constantRoots l) = 1 from he]
  apply Poly.equiv.injective
  simp

/-- A normalized piece has positive-degree modulus and a monic or vanishing polynomial.
Specialization preserves the input polynomial up to a nonzero scalar. -/
structure MonicPiece (m : Poly (K R 0)) (p : Step.BPoly (K R n))
    (u : Poly (K R 0) × Step.BPoly (K R n)) : Prop where
  divides : u.1 ∣ m
  positive : 0 < u.1.natDegree
  shape : u.2 = 0 ∨ (Poly.equiv u.2).Monic
  bound : u.2.natDegree ≤ p.natDegree
  associated : ∀ c : k, (Step.modelPoly (Model.constantHom k) u.1).IsRoot c →
    let h := Step.atRoot (val k) (Model.C k n c)
    Associated (Step.specialize h u.2) (Step.specialize h p)

private theorem root_of_dvd {F : Type} [Field F] [DecidableEq F] (j : F →+* k) {u m : Poly F}
    (hd : u ∣ m) {c : k} (hc : (Step.modelPoly j u).IsRoot c) : (Step.modelPoly j m).IsRoot c :=
  dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hc).trans (map_dvd _ hd))

private theorem atRoot_zero {m : Poly (K R 0)} {c : k}
    (hc : (Step.modelPoly (Model.constantHom k) m).IsRoot c) :
    Step.atRoot (val (n := n) k) (Model.C k n c) (m.map K.ofConst) = 0 := by
  rw [atRoot_ofConst]
  change Model.C k n ((Step.modelPoly (Model.constantHom k) m).eval c) = 0
  rw [hc, map_zero]

/-- Every piece of leading-coefficient normalization has a monic or zero polynomial and is
associated to the original polynomial at all its roots. -/
theorem monicPieces_spec [CharZero k] [IsAlgClosed k] (fuel : ℕ) {m : Poly (K R 0)}
    (hs : Squarefree (Step.modelPoly (Model.constantHom k) m)) (hm : 0 < m.natDegree)
    (hf : m.natDegree < fuel) (p : Step.BPoly (K R n)) (u) :
    u ∈ Step.monicPieces K.ofConst constantRoots fuel m p → MonicPiece k m p u := by
  induction fuel generalizing m p u with
  | zero => omega
  | succ fuel ih =>
    let mF := m.map (K.ofConst (n := n))
    let q := Step.reduceMod mF p
    let l := q.leadingCoeff
    let g := gcd m (constantRoots l)
    have hmd : mF.natDegree = m.natDegree := by
      rw [← Poly.natDegree_equiv, Poly.equiv_map, natDegree_map, Poly.natDegree_equiv]
    have hbound : q.natDegree ≤ p.natDegree := by
      simpa using natDegree_le_natDegree (Step.degree_reduceMod_le mF p)
    rw [Step.monicPieces]
    by_cases hq : q = 0
    · rw [ite_eq_left hq]
      rintro hu
      obtain rfl := List.mem_singleton.mp hu
      refine ⟨dvd_rfl, hm, Or.inl rfl, Nat.zero_le _, fun c hc => ?_⟩
      have he := Step.specialize_reduceMod _ (atRoot_zero (n := n) k hc) p
      change Step.specialize _ q = _ at he
      rw [hq] at he
      dsimp only
      rw [← he]
    · rw [ite_eq_right hq]
      dsimp only
      by_cases hg : g.natDegree = 0
      · rw [ite_eq_left hg]
        intro hu
        obtain rfl := List.mem_singleton.mp hu
        have h1 : gcd l mF = 1 := scalar_gcd_one k hs hg
        let v := (Step.bezout l mF).1
        let out := Step.reduceMod mF (Poly.C v * q)
        refine ⟨dvd_rfl, hm, Or.inr (Step.monic_reduce_bezout (hmd ▸ hm) q h1), ?_, ?_⟩
        · have he : out.natDegree ≤ (Poly.C v * q).natDegree := by
            simpa only [Poly.natDegree_equiv] using
              natDegree_le_natDegree (Step.degree_reduceMod_le mF (Poly.C v * q))
          apply he.trans (_root_.le_trans _ hbound)
          rw [← Poly.natDegree_equiv (Poly.C v * q), map_mul, Poly.equiv_C]
          simpa only [Poly.natDegree_equiv] using natDegree_C_mul_le v (Poly.equiv q)
        · intro c hc
          let h := Step.atRoot (val (R := R) (n := n) k) (Model.C k n c)
          have h0 : h mF = 0 := atRoot_zero k hc
          have hv := congrArg h (Step.bezout_spec l mF)
          rw [h1, map_one, map_add, map_mul, map_mul, h0, zero_mul, add_zero] at hv
          have hv' : h v ≠ 0 := fun hz => (one_ne_zero (α := M k n)) (by
            change h (Step.bezout l mF).1 = 0 at hz
            simpa [hz] using hv.symm)
          change Associated (Step.specialize h out) (Step.specialize h p)
          rw [show Step.specialize h out = C (h v) * Step.specialize h p by
            rw [show out = Step.reduceMod mF (Poly.C v * q) from rfl,
              Step.specialize_reduceMod h h0,
              map_mul, show Step.specialize h (Poly.C v) = C (h v) by simp [Step.specialize],
              show q = Step.reduceMod mF p from rfl, Step.specialize_reduceMod h h0]]
          exact associated_unit_mul_left _ _ (isUnit_C.mpr hv'.isUnit)
      · rw [ite_eq_right hg]
        have hl : l.natDegree < m.natDegree := by
          have ht : l = p.coeff q.natDegree % mF := by
            exact (Poly.coeff_natDegree q).symm.trans
              (Poly.coeff_map (· % mF) (EuclideanDomain.zero_mod _) p q.natDegree)
          rw [ht, ← hmd]
          exact Poly.natDegree_mod_lt _ (by omega)
        have deg := split_degrees k hs (Poly.leadingCoeff_ne_zero hq) hl (Nat.pos_of_ne_zero hg)
        have hg0 : g ≠ 0 := by rintro he; simp [he] at hg
        have dg : g ∣ m := gcd_dvd_left _ _
        have he := EuclideanDomain.mul_div_cancel' hg0 dg
        have sub {r} (dr : r ∣ m) (hr : 0 < r.natDegree) (hsz : r.natDegree < m.natDegree)
            (hu : u ∈ Step.monicPieces K.ofConst constantRoots fuel r q) : MonicPiece k m p u := by
          have sr := Squarefree.squarefree_of_dvd
            (map_dvd (Step.modelPoly (Model.constantHom k)) dr)
            hs
          have H := ih sr hr (by omega) q _ hu
          refine ⟨H.divides.trans dr, H.positive, H.shape, H.bound.trans hbound, ?_⟩
          intro c hc
          have h0 := atRoot_zero (n := n) k (root_of_dvd k _ (H.divides.trans dr) hc)
          simpa [q, mF, Step.specialize_reduceMod _ h0] using H.associated c hc
        intro hu
        rcases List.mem_append.mp hu with hx | hx
        · exact sub dg (Nat.pos_of_ne_zero hg) deg.1 hx
        · exact sub ⟨g, he.symm.trans (mul_comm _ _)⟩ deg.2.1 deg.2.2 hx

/-- A gcd piece gives a monic gcd after specializing at each root of its positive-degree
modulus. The common-divisor specification also covers two zero inputs. -/
structure GcdPiece (m : Poly (K R 0)) (a b : Step.BPoly (K R n))
    (u : Poly (K R 0) × Step.BPoly (K R n)) : Prop where
  divides : u.1 ∣ m
  positive : 0 < u.1.natDegree
  shape : u.2 = 0 ∨ (Poly.equiv u.2).Monic
  common : ∀ c : k, (Step.modelPoly (Model.constantHom k) u.1).IsRoot c →
    let h := Step.atRoot (val k) (Model.C k n c)
    ∀ w : (M k n)[X], w ∣ Step.specialize h u.2 ↔ w ∣ Step.specialize h a ∧ w ∣ Step.specialize h b

private theorem of_zero {m : Poly (K R 0)} {a : Step.BPoly (K R n)} {u}
    (H : MonicPiece k m a u) : GcdPiece k m a 0 u :=
  ⟨H.divides, H.positive, H.shape, fun c hc w => by
    simp [← (H.associated c hc).dvd_iff_dvd_right]⟩

/-- At every root of every piece the computed output is a gcd of the two specialized inputs. -/
theorem gcdAtRoots_spec [CharZero k] [IsAlgClosed k] (fuel : ℕ) {m : Poly (K R 0)}
    (hs : Squarefree (Step.modelPoly (Model.constantHom k) m)) (hm : 0 < m.natDegree)
    (a b : Step.BPoly (K R n)) (hf : b = 0 ∨ b.natDegree < fuel) (u) :
    u ∈ Step.gcdAtRoots K.ofConst constantRoots fuel m a b → GcdPiece k m a b u := by
  induction fuel generalizing m a b u with
  | zero =>
    obtain rfl := hf.resolve_right (Nat.not_lt_zero _)
    exact fun hu => of_zero k (monicPieces_spec k _ hs hm (Nat.lt_succ_self _) a u hu)
  | succ fuel ih =>
    by_cases hb : b = 0
    · subst b
      have hz : Step.reduceMod (m.map (K.ofConst (n := n))) 0 = 0 := by
        apply Poly.ext
        intro i
        simp [Step.reduceMod, Poly.coeff_map (· % _) (EuclideanDomain.zero_mod _)]
      have hbase : Step.monicPieces K.ofConst constantRoots (m.natDegree + 1) m
          (0 : Step.BPoly (K R n)) = [(m, 0)] := by
        rw [Step.monicPieces, ite_eq_left hz]
      rw [Step.gcdAtRoots, hbase]
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ite_true] using
        (fun hu => of_zero k (monicPieces_spec k _ hs hm (Nat.lt_succ_self _) a u hu))
    · have hf' := hf.resolve_left hb
      rw [Step.gcdAtRoots, List.mem_flatMap]
      rintro ⟨⟨v,d⟩, hmem, hu⟩
      have H := monicPieces_spec k _ hs hm (Nat.lt_succ_self _) b _ hmem
      have hv := H.positive
      have vs := Squarefree.squarefree_of_dvd
        (map_dvd (Step.modelPoly (Model.constantHom k)) H.divides)
        hs
      dsimp only at hu
      by_cases hd : d = 0
      · rw [ite_eq_left hd] at hu
        have A := monicPieces_spec k _ vs hv (Nat.lt_succ_self _) a _ hu
        refine ⟨A.divides.trans H.divides, A.positive, A.shape, ?_⟩
        intro c hc
        dsimp only
        intro w
        have H' := H.associated c (root_of_dvd k _ A.divides hc)
        dsimp only at H'
        rw [hd, map_zero] at H'
        rw [H'.eq_zero_iff.mp rfl, and_iff_left (dvd_zero _)]
        exact (A.associated c hc).dvd_iff_dvd_right
      · rw [ite_eq_right hd] at hu
        let vF := v.map (K.ofConst (n := n))
        let ar := Step.reduceMod vF a
        let r := Step.remainderMonic vF d (ar.natDegree+1) ar
        have hD := H.shape.resolve_left hd
        have hrd := Step.remainderMonic_degree vF hD (ar.natDegree+1) ar
          (Or.inr (Nat.lt_succ_self _))
        have f' : r = 0 ∨ r.natDegree < fuel := by
          by_cases hr : r = 0
          · exact Or.inl hr
          · have hl := natDegree_lt_natDegree ((map_ne_zero_iff _ Poly.equiv.injective).mpr hr) hrd
            change (Poly.equiv r).natDegree < (Poly.equiv d).natDegree at hl
            simp only [Poly.natDegree_equiv] at hl
            have Hbound : d.natDegree ≤ b.natDegree := H.bound
            exact Or.inr (by omega)
        have A := ih vs hv d r f' u hu
        refine ⟨A.divides.trans H.divides, A.positive, A.shape, ?_⟩
        intro c hc
        dsimp only
        intro w
        let h := Step.atRoot (val (R := R) (n := n) k) (Model.C k n c)
        have hc' := root_of_dvd k _ A.divides hc
        have h0 : h vF = 0 := atRoot_zero k hc'
        have hl : w ∣ Step.specialize h d ↔ w ∣ Step.specialize h b :=
          (H.associated c hc').dvd_iff_dvd_right
        have hr : Step.specialize h r = Step.specialize h a % Step.specialize h d := by
          rw [show r = Step.remainderMonic vF d (ar.natDegree+1) ar from rfl,
            Step.specialize_remainderMonic h h0 hD, show ar = Step.reduceMod vF a from rfl,
            Step.specialize_reduceMod h h0]
        change w ∣ Step.specialize h u.2 ↔ _
        rw [A.common c hc w, hr]
        constructor
        · rintro ⟨h₁,h₂⟩
          exact ⟨(EuclideanDomain.dvd_mod_iff h₁).mp h₂, hl.mp h₁⟩
        · rintro ⟨h₁,h₂⟩
          exact ⟨hl.mpr h₂, (EuclideanDomain.dvd_mod_iff (hl.mpr h₂)).mpr h₁⟩

end SympyProofs.Calculus.Antiderivative.Residue
