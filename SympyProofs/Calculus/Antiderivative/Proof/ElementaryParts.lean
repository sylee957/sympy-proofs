module

public import SympyProofs.Calculus.Antiderivative.Program.Elementary
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Clear
public import SympyProofs.Calculus.Antiderivative.Proof.Poles
public import SympyProofs.Calculus.Antiderivative.Proof.ResidueCriterion
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Hermite

/-! The computed separation of the special pole and the Hermite decomposition in the model. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial
open scoped Polynomial

variable {F : Type} [Field F] [DecidableEq F]

private theorem trim_special (l : List F) :
    Poly.ofList l = Poly.X ^ (l.takeWhile (· == 0)).length * Poly.ofList (l.dropWhile (· == 0)) ∧
    (l.dropWhile (· == 0) = [] ∨ (Poly.ofList (l.dropWhile (· == 0))).coeff 0 ≠ 0) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hc : c = 0
    · subst c
      simp only [List.takeWhile_cons, beq_self_eq_true, ↓reduceIte, List.length_cons,
        List.dropWhile_cons] at *
      refine ⟨?_, ih.2⟩
      apply Poly.equiv.injective
      have h := congrArg Poly.equiv ih.1
      simp only [Poly.equiv_ofList, map_mul, map_pow, Poly.equiv_X] at h ⊢
      simp [h, pow_succ', mul_assoc]
    · simp [hc]

private theorem special_split (den : Poly F) (hd : den ≠ 0) :
    let j := (den.coeffs.takeWhile (· == 0)).length
    Poly.X ^ j ∣ den ∧ (den / Poly.X ^ j).coeff 0 ≠ 0 := by
  let j := (den.coeffs.takeWhile (· == 0)).length
  let rest := Poly.ofList (den.coeffs.dropWhile (· == 0))
  obtain ⟨h, h₀⟩ := trim_special den.coeffs
  have he : den = Poly.X ^ j * rest := by simpa only [Poly.ofList_coeffs] using h
  have hx : (Poly.X : Poly F) ^ j ≠ 0 := by
    apply (map_ne_zero_iff Poly.equiv Poly.equiv.injective).mp
    simp
  have hr : rest.coeff 0 ≠ 0 := h₀.resolve_left fun hnil =>
    hd (by simpa [rest, hnil] using he)
  refine ⟨⟨rest, he⟩, ?_⟩
  change (den / Poly.X ^ j).coeff 0 ≠ 0
  rwa [he, mul_div_cancel_left₀ _ hx]

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

private theorem separate_den (a den : Poly F) (j : ℕ) :
    (Step.separatePole a den j).normalDen = den / Poly.X ^ j := by
  by_cases h : j = 0 <;> simp [Step.separatePole, h]

theorem poleOrder_spec (g : ReducedGen (K R n)) (den : Poly (K R n)) (hd : den ≠ 0) :
    let x := Poly.X ^ poleOrder g den
    x ∣ den ∧ IsCoprime x (den / x) := by
  cases g with
  | prim b => simp [poleOrder, isCoprime_one_left]
  | exp u =>
    obtain ⟨hdvd,h₀⟩ := special_split den hd
    refine ⟨hdvd, ?_⟩
    apply IsCoprime.pow_left
    let q := den / Poly.X ^ poleOrder (.exp u) den
    have hq : (Poly.equiv q).coeff 0 ≠ 0 := by simpa only [Poly.coeff_equiv, q, poleOrder] using h₀
    have hc : IsCoprime X (Poly.equiv q) :=
      irreducible_X.coprime_iff_not_dvd.mpr (fun h => hq (X_dvd_iff.mp h))
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← Poly.equiv_X,
      RingEquiv.symm_apply_apply] using hc.map Poly.equiv.symm.toRingHom

private theorem normal_separate (t : Tower R n) (g : ReducedGen (K R n))
    (hg : g.Admissible k t)
    (a den : Poly (K R n)) (hd : den ≠ 0) {p : (M k n)[X]} (hp : Prime p)
    (hpd : p ∣ Step.modelPoly (val k) (Step.separatePole a den (poleOrder g den)).normalDen) :
    ¬ p ∣ t.polyDerModel k g p := by
  cases g with
  | prim b => exact t.prime_normal_prim k b hg hp
  | exp u =>
    apply t.prime_normal_exp k u hg hp
    intro h₀
    obtain ⟨q, hq⟩ := hpd
    have h := congrArg (fun s : (M k n)[X] => s.coeff 0) hq
    simp [separate_den, h₀] at h
    apply (special_split den hd).2
    rw [← Poly.coeff_equiv]
    simpa only [Poly.equiv_div, map_pow, Poly.equiv_X, poleOrder] using h

private theorem normal_source (t : Tower R n) (g : ReducedGen (K R n)) (q : Poly (K R n))
    (hn : ∀ p : (M k n)[X], Prime p → p ∣ Step.modelPoly (val k) q →
      ¬ p ∣ t.polyDerModel k g p) :
    Step.normalFactors (K.derivation t.gens) (g.velocity t.D) q := by
  let : CharZero (K R n) := (val (R := R) (n := n) k).charZero
  intro r hr hrd hdr
  let f := val (R := R) (n := n) k
  have hs : (r.map f).Separable := (separable_map f).mpr
    (PerfectField.separable_iff_squarefree.mpr hr.irreducible.squarefree)
  have hpos : 0 < (r.map f).natDegree := by simpa using hr.irreducible.natDegree_pos
  obtain ⟨p, _, hp, hpr⟩ := exists_monic_irreducible_factor _ (not_isUnit_of_natDegree_pos _ hpos)
  have hpd := hpr.trans (map_dvd (mapRingHom f) hrd)
  have h := Extension.Residue.not_dvd_deriv (t.polyDerModel k g) hs.squarefree hp.prime hpr
    (hn p hp.prime hpd)
  apply h
  have he : (Step.modelDerivative (K.derivation t.gens) (g.velocity t.D) r).map f =
      t.polyDerModel k g (r.map f) := by
    obtain ⟨s, rfl⟩ := Poly.equiv.surjective r
    rw [← Step.polyDer_spec]
    exact t.modelPoly_polyDer k g s
  rw [← he]
  exact hpr.trans (map_dvd (mapRingHom f) hdr)

private theorem joinPoly_inj :
    Function.Injective (K.joinPolyHom : Poly (K R n) →+* K R (n+1)) := by
  intro a b h
  apply (Poly.interpret (K.equiv (R := R) (n := n))).injective
  apply RatFunc.algebraMap_injective (M R n)
  rw [← K.stepEquiv_joinPoly a, ← K.stepEquiv_joinPoly b, ← K.joinPolyHom_apply,
    ← K.joinPolyHom_apply, h]

/-- Evaluate rational functions over the lower computable field at the new generator. -/
private noncomputable def joinFraction : RatFunc (K R n) →+* K R (n+1) :=
  IsFractionRing.lift (g := K.joinPolyHom.comp (Poly.equiv (R := K R n)).symm.toRingHom) <| by
    intro p q h
    exact (Poly.equiv (R := K R n)).symm.injective (joinPoly_inj h)

private theorem joinFraction_fraction (a b : Poly (K R n)) :
    joinFraction (Step.fraction a b) = K.join a b := by
  simp only [joinFraction, Step.fraction, map_div₀, IsFractionRing.lift_algebraMap,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply,
    K.joinPolyHom_apply, K.join]

noncomputable local instance : Algebra ℤ (M k (n+1)) := Ring.toIntAlgebra _

private theorem model_exact (t : Tower R n) (g : ReducedGen (K R n))
    (z : Poly (K R n) × Poly (K R n)) :
    val k (joinFraction (Step.exactDerivative (K.derivation t.gens) (g.velocity t.D) z)) =
      (t.step g).modelD k (val k (K.join z.1 z.2)) := by
  rw [Step.exactDerivative, joinFraction_fraction, K.join, K.join, map_div₀, map_div₀,
    Derivation.leibniz_div]
  simp only [← K.joinPolyHom_apply, map_sub, map_mul]
  simp only [K.joinPolyHom_apply]
  rw [t.modelD_joinPoly k g, t.modelD_joinPoly k g]
  change _ / _ = _ ^ 2 • (_ • val k (K.joinPoly (Step.polyDer (K.derivation t.gens)
    (g.velocity t.D) z.1)) - _ • val k (K.joinPoly (Step.polyDer (K.derivation t.gens)
    (g.velocity t.D) z.2)))
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem model_exact_sum (t : Tower R n) (g : ReducedGen (K R n))
    (zs : List (Poly (K R n) × Poly (K R n))) :
    val k (joinFraction (zs.map
      (Step.exactDerivative (K.derivation t.gens) (g.velocity t.D))).sum) =
      (t.step g).modelD k (val k (zs.map (fun (p,q) => K.join p q)).sum) := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons, map_add, model_exact, ih]

private theorem joinPoly_X :
    K.joinPoly (Poly.X : Poly (K R n)) = K.gen := by
  apply (K.equiv.trans (Model.stepEquiv R n)).injective
  simp [K.stepEquiv_joinPoly, Poly.interpret_apply]

/-- Details needed by both the single-input integrator and the parametric residue stage. -/
structure PartsSpec (t : Tower R n) (g : ReducedGen (K R n)) (a den : Poly (K R n))
    (p : Parts R n) :
    Prop where
  residue : Residue.Input k t g p.proper p.normalDen
  coprime : IsCoprime ((X : (M k n)[X]) ^ poleOrder g den) (Step.modelPoly (val k) p.normalDen)
  identity : val k (K.join a den) = (t.step g).modelD k (val k p.exactPart) +
    val k (K.join p.proper p.normalDen) + val k (K.joinPoly p.laurent / K.gen ^ poleOrder g den)
  regular : ∀ z : (M k n)[X], Prime z → z ∣ Step.modelPoly (val k) p.normalDen →
    Extension.SimplePole.Integral z (Model.stepEquiv k n
      (val k (K.joinPoly p.laurent / K.gen ^ poleOrder g den)))

private theorem split_remainder (a d b : Poly (K R n)) (hd : d ≠ 0) (j : ℕ) :
    K.join a d + K.join b (Poly.X ^ j) = K.join (a % d) d +
      K.joinPoly ((a / d) * Poly.X ^ j + b) / K.gen ^ j := by
  let J := (K.joinPolyHom : Poly (K R n) →+* K R (n+1))
  have hx : (K.gen : K R (n+1)) ≠ 0 := by
    rw [← joinPoly_X, ← K.joinPolyHom_apply]
    apply (map_ne_zero_iff _ joinPoly_inj).mpr
    exact (map_ne_zero_iff Poly.equiv Poly.equiv.injective).mp (by simp)
  have hjx : J Poly.X = K.gen := K.joinPolyHom_apply _ |>.trans joinPoly_X
  have hjd : J d ≠ 0 := (map_ne_zero_iff _ joinPoly_inj).mpr hd
  have h := congrArg J (EuclideanDomain.div_add_mod a d)
  simp only [map_add, map_mul] at h
  simp only [K.join, ← K.joinPolyHom_apply]
  change J a / J d + J b / J (Poly.X ^ j) = J (a % d) / J d +
    J ((a / d) * Poly.X ^ j + b) / K.gen ^ j
  simp only [map_add, map_mul, map_pow, hjx, add_div, mul_div_cancel_right₀ _ (pow_ne_zero j hx)]
  rw [← h, add_div, mul_div_cancel_left₀ _ hjd]
  abel

omit [CharZero k] in
private theorem laurent_regular (a d : Poly (K R n)) (j : ℕ)
    (hc : IsCoprime (Poly.X ^ j) d) {z : (M k n)[X]} (hz : Prime z)
    (hzd : z ∣ Step.modelPoly (val k) d) :
    Extension.SimplePole.Integral z (Model.stepEquiv k n (val k (K.joinPoly a / K.gen ^ j))) := by
  refine ⟨Step.modelPoly (val k) a, X ^ j, ?_, ?_⟩
  · intro hd
    exact hz.not_isUnit ((hc.map (Step.modelPoly (val k))).isUnit_of_dvd' (by simpa using hd) hzd)
  · simp [val_joinPoly, pow_ne_zero j (RatFunc.X_ne_zero : (RatFunc.X : RatFunc (M k n)) ≠ 0)]

/-- The computed Hermite part, proper normal fraction, and Laurent numerator recover the input. -/
theorem parts_spec (t : Tower R n) (g : ReducedGen (K R n)) (hg : g.Admissible k t)
    (a den : Poly (K R n)) (hd : den ≠ 0) :
    PartsSpec k t g a den (parts t.D (g.velocity t.D) den (poleOrder g den) a) := by
  let : CharZero (K R n) := (val (R := R) (n := n) k).charZero
  let j := poleOrder g den
  let dx := g.velocity t.D
  let sep := Step.separatePole a den j
  let red := Step.hermite t.D dx sep.normalNum sep.normalDen
  obtain ⟨hdiv,hcop⟩ := poleOrder_spec g den hd
  have hn (p : (M k n)[X]) := normal_separate k t g hg a den hd (p := p)
  have hr := Step.hermite_spec (K.derivation t.gens) dx sep.normalNum sep.normalDen
    (normal_source k t g sep.normalDen hn)
  change Step.fraction sep.normalNum sep.normalDen =
    (red.exactTerms.map (Step.exactDerivative (K.derivation t.gens) dx)).sum +
    Step.fraction red.numerator red.denominator ∧ Squarefree (Poly.equiv red.denominator) ∧
    Poly.equiv red.denominator ∣ Poly.equiv sep.normalDen at hr
  obtain ⟨he,hs,hc⟩ := hr
  have hmap := map_dvd (mapRingHom (val (R := R) (n := n) k)) hc
  have hrd : red.denominator ≠ 0 := (map_ne_zero_iff _ Poly.equiv.injective).mp hs.ne_zero
  constructor
  · refine ⟨((separable_map (val k)).mpr (PerfectField.separable_iff_squarefree.mpr hs)).squarefree,
      fun z hz hzd => hn z hz (hzd.trans hmap), ?_⟩
    change ((Poly.equiv (red.numerator % red.denominator)).map _).degree <
      ((Poly.equiv red.denominator).map _).degree
    simpa only [degree_map, Poly.equiv_mod] using
      degree_mod_lt (Poly.equiv red.numerator) hs.ne_zero
  · apply IsCoprime.of_isCoprime_of_dvd_right _ hmap
    have h : IsCoprime (Poly.X ^ j) sep.normalDen := by simpa only [sep, separate_den] using hcop
    simpa using h.map (Step.modelPoly (val k))
  · have H := congrArg (fun z : RatFunc (K R n) => val k (joinFraction z))
      (Step.separatePole_spec a den j hdiv hcop).symm
    change val k (joinFraction (Step.fraction a den)) = val k (joinFraction
      (Step.fraction sep.normalNum sep.normalDen + Step.fraction sep.specialNum (Poly.X ^ j))) at H
    rw [he] at H
    simp only [map_add, joinFraction_fraction] at H
    rw [model_exact_sum k t g red.exactTerms] at H
    change val k (K.join a den) = _ at H
    rw [H, add_assoc, ← map_add, split_remainder _ _ _ hrd, map_add, ← add_assoc]
    rfl
  · intro z hz hzd
    apply laurent_regular k _ sep.normalDen j _ hz (hzd.trans hmap)
    simpa only [sep, separate_den] using hcop

end SympyProofs.Calculus.Antiderivative.Elementary
