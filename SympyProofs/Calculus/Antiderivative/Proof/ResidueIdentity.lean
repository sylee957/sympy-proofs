module

public import SympyProofs.Calculus.Antiderivative.Proof.ResidueCover
public import SympyProofs.Calculus.Antiderivative.Proof.UniformResidue

/-! Sum the logarithmic terms and lower correction of the Rothstein–Trager residue
partition, and identify their derivative in the model tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

local notation "ι" => algebraMap (M k n)[X] (RatFunc (M k n))

/-- The constants whose residues give nonconstant gcds. -/
noncomputable def roots {a d e : Poly (K R n)} (k : Type) [Field k] [Algebra R k]
    [FaithfulSMul R k] : Finset k := by
  classical
  exact (Step.modelPoly (Model.constantHom k)
    (constantRoots (residuePolynomial a d e))).roots.toFinset

/-- The lower correction is minus the sum of the scalar residues weighted by their gcd degrees. -/
theorem correction_sum [CharZero k] [IsAlgClosed k] {a d e : Poly (K R n)} (hd : d ≠ 0)
    (hz : residuePolynomial a d e ≠ 0) :
    Model.constantHom k ((rawPieces a d e).map correction).sum =
      ∑ c ∈ roots (a := a) (d := d) (e := e) k, -((residueGcd k a d e c).natDegree : k) * c := by
  classical
  rw [roots, ← rawPieces_sum k a d e hz, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  obtain ⟨m,p⟩ := u
  let P := Step.modelPoly (Model.constantHom (R := R) k) m
  have H := rawPieces_spec k a d e hz hu
  have sq : Squarefree P := Squarefree.squarefree_of_dvd (map_dvd _ H.divides)
    (constantRoots_squarefree k hz)
  rw [Function.comp_apply, correction_spec k m p H.positive (IsAlgClosed.splits P)]
  change _ = ∑ c ∈ P.roots.toFinset, _
  rw [Finset.sum_congr rfl (fun c hc => congrArg (fun t : ℕ => -(t:k) * c) <|
    (gcdPiece_value k hd H ((mem_roots sq.ne_zero).mp (Multiset.mem_toFinset.mp hc))).2),
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (nodup_roots (PerfectField.separable_iff_squarefree.mpr sq)),
    Multiset.map_id']

/-- Every logarithm argument is nonzero at every selected residue. -/
theorem rawPieces_regular [CharZero k] [IsAlgClosed k] {a d e : Poly (K R n)} (hd : d ≠ 0)
    (hz : residuePolynomial a d e ≠ 0) {u} (hu : u ∈ rawPieces a d e) : (rootSum u).Regular k := by
  obtain ⟨m,p⟩ := u
  have H := rawPieces_spec k a d e hz hu
  have sq := Squarefree.squarefree_of_dvd
    (_root_.map_dvd (Step.modelPoly (Model.constantHom k)) H.divides)
    (constantRoots_squarefree k hz)
  refine ⟨sq.ne_zero, fun c hc z => ?_⟩
  have ha := rootSum_argAt k m p c
  rw [z, map_zero, (gcdPiece_value k hd H hc).1] at ha
  have hd' : Step.modelPoly (val k) d ≠ 0 :=
    (map_ne_zero_iff _ ((map_injective _ (val_injective (R := R) k)).comp
      Poly.equiv.injective)).mpr hd
  exact RatFunc.algebraMap_ne_zero (Extension.Residue.mgcd_monic (a := _) hd').ne_zero ha.symm

/-- The derivative of all returned logarithms in the one-step rational-function presentation. -/
theorem deriv_sum [CharZero k] [IsAlgClosed k] (t : Tower R n) (g : ReducedGen (K R n))
    {a d e : Poly (K R n)} (hd : d ≠ 0) (hz : residuePolynomial a d e ≠ 0) :
    Model.stepEquiv k n
      (((rawPieces a d e).map rootSum).map (RootSum.deriv k (t.step g))).sum =
      ∑ c ∈ roots (a := a) (d := d) (e := e) k, RatFunc.C (Model.C k n c) *
        (ι (t.polyDerModel k g (residueGcd k a d e c)) / ι (residueGcd k a d e c)) := by
  classical
  rw [roots, ← rawPieces_sum k a d e hz, map_list_sum, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  obtain ⟨m,p⟩ := u
  have H := rawPieces_spec k a d e hz hu
  have sq := Squarefree.squarefree_of_dvd
    (_root_.map_dvd (Step.modelPoly (Model.constantHom k)) H.divides)
    (constantRoots_squarefree k hz)
  simp only [Function.comp_apply, RootSum.deriv, show (rootSum (m,p)).weight = 1 from rfl,
    map_one,
    one_mul, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have ha := rootSum_argAt k m p c
  rw [(gcdPiece_value k hd H ((mem_roots sq.ne_zero).mp (Multiset.mem_toFinset.mp hc))).1] at ha
  rw [map_mul, map_div₀, Tower.stepEquiv_modelD, ha]
  rw [← Model.includeVars_C k (Nat.le_succ n) c, Model.stepEquiv_include]
  change RatFunc.C _ * (Extension.extend (t.polyDerModel k g) (ι _) / ι _) = _
  rw [Extension.extend_poly]

/-- The inputs to the normal simple-pole residue calculation. -/
structure Input (t : Tower R n) (g : ReducedGen (K R n)) (a d : Poly (K R n)) : Prop where
  squarefree : Squarefree (Step.modelPoly (val k) d)
  normal : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) d → ¬ p ∣ t.polyDerModel k g p
  proper : (Step.modelPoly (val k) a).degree < (Step.modelPoly (val k) d).degree

theorem Input.den_ne_zero {t : Tower R n} {g : ReducedGen (K R n)} {a d : Poly (K R n)}
    (h : Input k t g a d) : d ≠ 0 := fun hz => h.squarefree.ne_zero (hz ▸ map_zero _)

theorem Input.resultant_ne_zero [CharZero k] {t : Tower R n} {g : ReducedGen (K R n)}
    {a d : Poly (K R n)} (h : Input k t g a d) :
    residuePolynomial a d (Step.polyDer t.D (g.velocity t.D) d) ≠ 0 := by
  apply residuePolynomial_ne_zero_of_coprime k (h.den_ne_zero k)
  rw [Tower.modelPoly_polyDer]
  exact isCoprime_of_prime_dvd (fun bad => h.squarefree.ne_zero bad.1)
    fun p hp hpD => Extension.Residue.not_dvd_deriv (t.polyDerModel k g) h.squarefree hp hpD
      (h.normal p hp hpD)

private theorem pieces_identity [CharZero k] [IsAlgClosed k] (t : Tower R n)
    (g : ReducedGen (K R n))
    (a d : Poly (K R n)) (h : Input k t g a d)
    (e := Step.polyDer t.D (g.velocity t.D) d)
    (he : e = Step.polyDer t.D (g.velocity t.D) d := by rfl)
    (ps := rawPieces a d e) (hp : ps = rawPieces a d e := by rfl)
    (hc : (ps.map fun p => p.1.natDegree * p.2.natDegree).sum = d.natDegree) :
    val k (K.join a d) = ((ps.map rootSum).map (RootSum.deriv k (t.step g))).sum +
      val k (K.lift ((g.velocity t.D).coeff 1 * K.ofConst (ps.map correction).sum)) := by
  classical
  let S := roots (a := a) (d := d) (e := e) k
  let emb : k ↪ M k n := ⟨Model.C k n, (Model.C k n).injective⟩
  let δ := t.polyDerModel k g
  let A := Step.modelPoly (val k) a
  let D := Step.modelPoly (val k) d
  let tw := val k ((g.velocity t.D).coeff 1)
  have agree (z : k) : Extension.Residue.resGcd δ A D (emb z) = residueGcd k a d e z := by
    simp only [Extension.Residue.resGcd, residueGcd, he, Tower.modelPoly_polyDer]
    rfl
  have hz : residuePolynomial a d e ≠ 0 := he ▸ h.resultant_ne_zero k
  have hd := h.den_ne_zero k
  have deg : D.natDegree = d.natDegree := by simp [D, natDegree_map]
  have tot : ∑ x ∈ S.map emb, (Extension.Residue.resGcd δ A D x).natDegree = D.natDegree := by
    rw [Finset.sum_map, deg]
    simp only [agree]
    exact (accounted_spec k hd hz).symm.trans (hp ▸ hc)
  have id := Extension.Residue.logPart_identity δ tw (fun _ => t.degree_polyDerModel k g)
    h.squarefree h.normal
    h.proper (S.map emb) tot
  have agree' (z : k) : Extension.Residue.resGcd δ (Step.modelPoly (val k) a)
      (Step.modelPoly (val k) d) (emb z) = residueGcd k a d e z := agree z
  simp only [Finset.sum_map, agree'] at id
  apply (Model.stepEquiv k n).injective
  rw [K.join, map_div₀, map_div₀, val_joinPoly, val_joinPoly, map_add, hp, deriv_sum k t g hd hz,
    val_lift, Model.stepEquiv_include, map_mul, ← Model.C_constantHom, correction_sum k hd hz]
  change ι A / ι D = _ + RatFunc.C (tw * Model.C k n (∑ c ∈ S, _))
  rw [id]
  simp only [map_sum, map_mul, map_neg, map_natCast, neg_mul, Finset.sum_neg_distrib, mul_neg,
    sub_eq_add_neg, emb, S, δ, Function.Embedding.coeFn_mk]
  ring

/-- A successful logarithmic step returns regular arguments and the proven rational-function
identity on every proper fraction with squarefree normal denominator. -/
theorem logPart_sound [CharZero k] [IsAlgClosed k] (t : Tower R n) (g : ReducedGen (K R n))
    {a d : Poly (K R n)} (h : Input k t g a d) {logs : List (RootSum R (n+1))} {corr : K R n}
    (hs : logPart a d (Step.polyDer t.D (g.velocity t.D) d) ((g.velocity t.D).coeff 1) =
      some (logs,corr)) : (∀ s ∈ logs, s.Regular k) ∧
      val k (K.join a d) =
        (logs.map (RootSum.deriv k (t.step g))).sum + val k (K.lift corr) := by
  let e := Step.polyDer t.D (g.velocity t.D) d
  rw [logPart] at hs
  split at hs
  · rename_i ht
    have ha : a = 0 := by
      rcases (show a = 0 ∨ d.natDegree = 0 by simpa using ht) with h | h₀
      · exact h
      · have H := h.proper
        have deg : (Step.modelPoly (val k) d).degree = 0 := by
          rw [degree_eq_natDegree h.squarefree.ne_zero]
          simp [natDegree_map, h₀]
        rw [deg] at H
        have hz := degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp H)
        exact (map_eq_zero_iff _ ((map_injective _ (val_injective (R := R) k)).comp
          Poly.equiv.injective)).mp (show Step.modelPoly (val k) a = 0 from hz)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    have hzero : K.joinPoly (0 : Poly (K R n)) = 0 := by
      rw [K.joinPoly, ← Poly.eval_equiv, Poly.equiv_map]
      simp
    simp [ha, K.join, hzero]
  · cases hu : uniformPart a d e with
    | some out =>
      rw [hu] at hs
      obtain rfl : out = (logs,corr) := Option.some.inj hs
      exact uniformPart_step k t g (h.den_ne_zero k) hu
    | none =>
      rw [hu] at hs
      dsimp only at hs
      rw [rawPieces_filter k (h.den_ne_zero k) (h.resultant_ne_zero k)] at hs
      split at hs
      · rename_i hc
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hs)
        refine ⟨?_, pieces_identity k t g a d h e rfl _ rfl hc⟩
        intro s hs
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hs
        exact rawPieces_regular k (h.den_ne_zero k) (h.resultant_ne_zero k) hu
      · contradiction

end SympyProofs.Calculus.Antiderivative.Residue
