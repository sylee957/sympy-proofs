module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Coordinates
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Gauss

/-! Completeness of factorization in a rational function field over the ground constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Factor

private theorem decode_zero {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]
    (f : F →+* G) (vs : List (Poly G)) (bs : List ℕ) :
    decode f vs bs 0 = 0 := by simp [decode]

private theorem proper_C_mul {F : Type} [Field F] [DecidableEq F] {p q : Poly F}
    (good : proper p q) {a : F} (ha : a ≠ 0) : proper p (Poly.C a * q) := by
  obtain ⟨hq0, hlt, hd⟩ := (proper_iff _ _).mp good
  have deg : (Poly.C a * q).natDegree = q.natDegree := by
    rw [← Poly.natDegree_equiv, map_mul, Poly.equiv_C, Polynomial.natDegree_C_mul ha,
      Poly.natDegree_equiv]
  have unit : IsUnit (Poly.C a) := (isUnit_iff_dvd_one.mpr
    ⟨Poly.C a⁻¹, by rw [← Poly.C_mul, mul_inv_cancel₀ ha, Poly.C_one]⟩)
  exact (proper_iff _ _).mpr ⟨deg ▸ hq0, deg ▸ hlt, unit.mul_left_dvd.mpr hd⟩

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

private theorem natDegree_interpret {n : ℕ} (p : Poly (K R n)) :
    (Poly.interpret (overConstants n) p).natDegree = p.natDegree := by
  rw [Poly.interpret_apply, Polynomial.natDegree_map, Poly.natDegree_equiv]

/-- A proper factor over the rational function field lifts to a divisor of the cleared
multivariate polynomial with a proper restored image. -/
private theorem lifted_divisor {n : ℕ} (p : Poly (K R n)) (P : MvPolynomial (Fin (n+1)) (K R 0))
    (d : K R n) (clear : parameterHom n P =
      Poly.interpret (overConstants n) (Poly.C d * p))
    (hdeg : 2 ≤ p.natDegree) (hI : ¬Irreducible p) :
    ∃ B, B ∣ P ∧ proper p (restoreHom (descend (RingHom.id (K R n)))
      (parameters (RingHom.id (K R n)) [Poly.X]) (n+1) B) := by
  classical
  let Γ := K R 0
  let A := MvPolynomial (Fin n) Γ
  let L := M Γ n
  let I := Poly.interpret (overConstants (R := R) n)
  have deg := natDegree_interpret p
  change (I p).natDegree = p.natDegree at deg
  have hn : I p ≠ 0 := fun h => by simp [h] at deg; omega
  have nh := (I p).not_isUnit_of_natDegree_pos (by omega)
  have reduc : ¬Irreducible (I p) := fun h => hI ((MulEquiv.irreducible_iff I).mp h)
  rw [Polynomial.irreducible_iff_lt_natDegree_lt hn nh] at reduc
  push Not at reduc
  obtain ⟨q, _, hq, hdiv⟩ := reduc
  rw [Finset.mem_Ioc] at hq
  have q0 : q ≠ 0 := fun e => by simp [e] at hq
  have dv : q ∣ ((Model.splitPolynomial Γ n) P).map (algebraMap A L) := by
    change q ∣ parameterHom n P
    rw [clear, map_mul]
    exact hdiv.trans (dvd_mul_left _ _)
  let _ : NormalizedGCDMonoid A := Classical.choice inferInstance
  obtain ⟨b, hb, hassoc, hbdeg⟩ := lift_fraction_divisor ((Model.splitPolynomial Γ n) P) q q0 dv
  let B := (Model.splitPolynomial Γ n).symm b
  have divB : B ∣ P := by simpa [B] using map_dvd (Model.splitPolynomial Γ n).symm hb
  let Q := restoreHom (descend (RingHom.id (K R n))) (parameters (RingHom.id (K R n)) [Poly.X])
    (n+1) B
  have eqQ : I Q = b.map (algebraMap A L) := by
    rw [show I Q = parameterHom n B from restore_parameterHom _ _, parameterHom]
    change ((Model.splitPolynomial Γ n) ((Model.splitPolynomial Γ n).symm b)).map _ = _
    rw [AlgEquiv.apply_symm_apply]
  have Qdeg : Q.natDegree = q.natDegree := by
    rw [← natDegree_interpret]
    change (I Q).natDegree = _
    rw [eqQ, Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A L), hbdeg]
  have dvdQ : Q ∣ p := by
    have hd' : I Q ∣ I p := eqQ ▸ hassoc.dvd_iff_dvd_left.mpr hdiv
    simpa using map_dvd I.symm hd'
  refine ⟨B, divB, ?_⟩
  change proper p Q
  exact (proper_iff _ _).mpr ⟨by omega, by omega, dvdQ⟩

private theorem encoded_search {n : ℕ} [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]
    (p : Poly (K R n)) (ts : List (List ℕ × K R 0)) (hl : ∀ t ∈ ts, t.1.length = n+1)
    (d : K R n) (hd : d ≠ 0) (hdeg : 2 ≤ p.natDegree) (hI : ¬Irreducible p)
    (clear : termsValue (descend (RingHom.id (K R n))) (parameters (RingHom.id (K R n)) [Poly.X])
      ts = Poly.C d * p) :
    let f := RingHom.id (K R n)
    let bs := radices (n+1) ts
    (subsetFactor (decode (descend f) (parameters f [Poly.X]) bs) p 1
      (ConstantFactors.factors (substitute bs ts))).isSome := by
  let k := n+1
  let P := sparsePolynomial k ts
  let bs := radices k ts
  let f := descend (RingHom.id (K R n))
  let vs := parameters (RingHom.id (K R n)) [Poly.X]
  let restored := restoreHom f vs k
  let subst := substituteHom (F := K R 0) bs k
  have len : bs.length = k := by simp [bs, radices]
  have cp : restored P = Poly.C d * p := (restore_eq f vs ts hl).trans clear
  have cmodel : parameterHom n P = Poly.interpret (overConstants n) (Poly.C d * p) :=
    (restore_parameterHom n P).symm.trans (congrArg _ cp)
  obtain ⟨B, hdB, hgood⟩ := lifted_divisor p P d cmodel hdeg hI
  change proper p (restored B) at hgood
  have hp : p ≠ 0 := fun he => by simp [he] at hdeg
  have hP : P ≠ 0 := by
    intro he
    rw [he, map_zero] at cp
    exact (mul_ne_zero (fun h => hd (Poly.C_injective (h.trans Poly.C_zero.symm))) hp) cp.symm
  let dec := decode f vs bs
  have bounds := sparse_bounds ts k
  have recover : dec (subst P) = restored P := decode_substituteHom f vs bs len P bounds
  have valid : dec (subst B) = restored B :=
    decode_substituteHom f vs bs len B (bounds_of_dvd hP hdB bs bounds)
  have pos := ((proper_iff _ _).mp hgood).1
  have b0 : subst B ≠ 0 := by
    intro h
    rw [h, show dec 0 = 0 from decode_zero _ _ _] at valid
    simp [← valid] at pos
  have p0 : subst P ≠ 0 := by
    intro h
    rw [h, show dec 0 = 0 from decode_zero _ _ _, cp] at recover
    exact (mul_ne_zero (fun h => hd (Poly.C_injective (h.trans Poly.C_zero.symm))) hp) recover.symm
  change (subsetFactor dec p 1 (ConstantFactors.factors (substitute bs ts))).isSome
  rw [substitute_eq bs len ts hl]
  apply subsetFactor_of_dvd dec p _ p0 (normalize (subst B)) (normalize_idem _)
    (normalize_dvd_iff.mpr (map_dvd subst hdB))
  change proper p (decode f vs bs (normalize (subst B)))
  rw [Poly.normalize_eq_C_mul, decode_C_mul, show decode f vs bs (subst B) = _ from valid]
  exact proper_C_mul hgood ((map_ne_zero_iff f f.injective).mpr
    (inv_ne_zero (Poly.leadingCoeff_ne_zero b0)))

/-- A reducible polynomial always produces a checked divisor over its tower coefficient field. -/
theorem towerDivisor_complete [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)]
    {n : ℕ} (p : Poly (K R n)) (hd : 2 ≤ p.natDegree) (hI : ¬Irreducible p) :
    ∃ q, towerDivisor p = some q ∧ proper p q := by
  let ts := p.coeffs.zipIdx.filterMap fun (a,i) => if a = 0 then none else some ([i], a)
  have wid : ∀ t ∈ ts, t.1.length = 1 := by
    intro t ht
    obtain ⟨⟨c,i⟩, _, hc⟩ := List.mem_filterMap.mp ht
    change (if c = 0 then none else some ([i], c)) = some t at hc
    split at hc
    · contradiction
    · cases hc; rfl
  obtain ⟨d, hn, hc⟩ := clear_polynomial p
  have success := encoded_search p (clearTerms ts) (clearTerms_width _ _ wid) d hn hd hI hc
  change (towerDivisor p).isSome at success
  cases h : towerDivisor p with
  | none => simp [h] at success
  | some q => exact ⟨_, rfl, subsetFactor_proper _ _ _ h⟩

end Factor

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)] {n : ℕ}

/-- Every factor of the computed tower factorization is irreducible over the full coefficient
field of rational functions in the lower parameters. -/
theorem factorTower_irreducible (p : Poly (K R n)) (hp : p ≠ 0) (q : Poly (K R n))
    (hq : q ∈ factorTower p) : Irreducible q := by
  cases n with
  | zero => exact (LawfulConstantFactors.irreducible p hp q hq).2
  | succ n => exact Factor.split_irreducible _ Factor.towerDivisor_complete _ _ (le_refl _) hq

end SympyProofs.Calculus.Antiderivative
