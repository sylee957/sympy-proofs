module

public import SympyProofs.Calculus.Antiderivative.Proof.Verify.Modulus

/-! The executable residue-algebra trace differentiates every regular root sum. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.RootSum

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Evaluate a logarithmic argument at one model root. -/
private noncomputable def atRoot (c : k) : Poly (K R n) →+* M k n :=
  (evalRingHom (Model.C k n c)).comp (Step.modelPoly (val k))

private theorem atRoot_arg (s : RootSum R n) (c : k) : atRoot k c s.arg = s.argAt k c :=
  eval_map ..

private theorem atRoot_argD (ds : List (K R n)) (s : RootSum R n) (c : k) :
    atRoot k c (s.arg.map (K.der ds)) = Model.derivation k (ds.map (val k)) (s.argAt k c) := by
  let _ : Differential (M k n) := ⟨Model.derivation k (ds.map (val k))⟩
  let P := Step.modelPoly (val k) s.arg
  have hp : Step.modelPoly (val k) (s.arg.map (K.der ds)) = Differential.mapCoeffs P := by
    ext i
    simp [P, Poly.coeff_map (K.der ds) (K.der_zero _)]
    exact (val_der k ds _).trans (Model.derivation_apply k _ _).symm
  have hD : Differential.deriv (Model.C k n c) = 0 := Model.derivation_C k _ _
  have h := Differential.deriv_aeval_eq (Model.C k n c) P
  simp only [coe_aeval_eq_eval,hD,mul_zero,add_zero] at h
  rw [← atRoot_arg]
  change (Step.modelPoly _ _).eval _ = Differential.deriv (P.eval _)
  rw [hp,h]

variable [CharZero k] [IsAlgClosed k]

/-- Exact verification succeeds on every regular root sum and returns its formal derivative. -/
theorem differentiateAlong_spec (ds : List (K R n)) (s : RootSum R n) (h : s.Regular k) :
    ∃ x, s.differentiateAlong ds = some x ∧ val k x = s.derivAlong k ds := by
  classical
  let p := s.liftedRadical
  let P := s.constantRadical k
  let ι := Model.C k n
  let Q := Step.modelPoly (val k) p
  let S := P.roots.toFinset
  have hs := squarefree_radical k h
  have pdef : (Step.squarefreeParts s.modulus).1.map (K.ofConst (n := n)) = p := rfl
  have hne := regular_modulus_ne_zero k h
  have hS : S.card = p.natDegree := by
    exact (Multiset.toFinset_card_of_nodup (nodup_roots
      (PerfectField.separable_iff_squarefree.mpr hs))).trans
      ((IsAlgClosed.splits P).natDegree_eq_card_roots.symm.trans (radical_degree k))
  have hQ : Q = P.map ι := model_liftedRadical k s
  have hL : Q.leadingCoeff = val k p.leadingCoeff := by simp [Q]
  have hM : Q.leadingCoeff = ι P.leadingCoeff := by rw [hQ,leadingCoeff_map]
  have he (c : k) (hc : c ∈ S) : atRoot k c p = 0 := by
    change Q.eval (ι c) = 0
    rw [hQ,eval_map_apply]
    exact (map_zero ι) ▸ congrArg ι ((mem_roots hs.ne_zero).mp (Multiset.mem_toFinset.mp hc))
  have bez := Step.bezout_spec s.arg p
  have hg := normalize_eq_one.mpr
    ((gcd_isUnit_iff_isRelPrime ..).mpr (radical_coprime k h).isRelPrime)
  rw [normalize_gcd] at hg
  rw [hg] at bez
  by_cases hp0 : p.natDegree = 0
  · have empty : S = ∅ := Finset.card_eq_zero.mp (hS.trans hp0)
    refine ⟨0,?_,?_⟩
    · simp [differentiateAlong, hne, pdef, hp0]
    · rw [derivAlong, ← radical_roots k h]
      rw [show (s.constantRadical k).roots.toFinset = ∅ from empty,
        Finset.sum_empty,mul_zero,map_zero]
  let A := (Step.bezout s.arg p).1
  let v := (Poly.X * s.arg.map (K.der ds) * A * p.derivative) % p
  let V := Step.modelPoly (val k) v
  let f (c : k) := ι c * (Model.derivation k (ds.map (val k)) (s.argAt k c) / s.argAt k c)
  have hQne : Q ≠ 0 := hQ ▸ (Polynomial.map_ne_zero hs.ne_zero)
  have hdeg : V.degree < S.card := by
    rw [hS,← Poly.natDegree_equiv,← natDegree_map (p := Poly.equiv p) (val k)]
    change ((Poly.equiv (_ % p)).map (val k)).degree < Q.natDegree
    rw [Poly.equiv_mod,map_mod,← degree_eq_natDegree hQne]
    exact degree_mod_lt _ hQne
  have hv (c : k) (hc : c ∈ S) : V.eval (ι c) = f c * Q.derivative.eval (ι c) := by
    let E := atRoot (R := R) (n := n) k c
    have hb := congrArg E bez
    have hemp : E p = 0 := he c hc
    simp only [map_add,map_mul,hemp,zero_mul,add_zero,map_one] at hb
    change E v = _
    rw [show v = _ from rfl,Step.map_mod_of_zero E (he c hc),map_mul,map_mul,map_mul]
    have ha : E s.arg = s.argAt k c := atRoot_arg k s c
    have harg := h.2 c ((radical_root k s c).mp ((mem_roots hs.ne_zero).mp
      (Multiset.mem_toFinset.mp hc)))
    have inv : E A = (s.argAt k c)⁻¹ := by
      apply mul_left_cancel₀ harg
      rw [mul_inv_cancel₀ harg,← ha]
      exact hb
    have hd : E p.derivative = Q.derivative.eval (ι c) := by
      simp [E,atRoot,Q,ι,derivative_map]
    have hX : E Poly.X = ι c := by simp [E,atRoot,ι]
    rw [hd,hX,atRoot_argD,inv]
    simp [f,div_eq_mul_inv,mul_assoc]
  have hl := (map_ne_zero_iff ι ι.injective).mpr (leadingCoeff_ne_zero.mpr hs.ne_zero)
  have tr := coefficient_trace ι.injective.injOn hl (hQ.trans (map_eq_nodal ι hs)) hdeg f hv
  rw [hS,← hM,hL] at tr
  refine ⟨K.ofConst s.weight * v.coeff (p.natDegree-1) / p.leadingCoeff,?_,?_⟩
  · simp [differentiateAlong,hne,pdef,hp0,bez,A,v]
  · rw [derivAlong,← radical_roots k h,map_div₀,map_mul,mul_div_assoc]
    change _ * _ = _ * ∑ c ∈ S, f c
    congr 1
    simpa [V] using tr

/-- Exact differentiation agrees with the model derivative of each regular root sum. -/
theorem differentiate_spec (t : Tower R n) (s : RootSum R n) (h : s.Regular k) :
    ∃ x, s.differentiate t = some x ∧ val k x = s.deriv k t :=
  differentiateAlong_spec k t.gens s h

end SympyProofs.Calculus.Antiderivative.RootSum
