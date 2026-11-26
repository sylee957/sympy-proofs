module

public import SympyProofs.Calculus.Antiderivative.Program.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Resultant
public import SympyProofs.Calculus.Antiderivative.Spec.Split
import Mathlib.Algebra.CharZero.Infinite

/-! Coefficient slices recover exactly the constant roots of a polynomial over the tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Residue

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- A list of successive powers used to express polynomial evaluation as a linear combination. -/
private def powers (z a : k) : ℕ → List k
  | 0 => []
  | m + 1 => a :: powers z (a * z) m

private theorem eval_powers {G : Type} [Field G] (j : M k n →+* G) (ι : k →+* G)
    (hj : ∀ b, j (Model.C k n b) = ι b) (r : List (K R n)) (z a : k) :
    j (Model.linearCombination k (powers k z a r.length) r) =
      ι a * (Step.modelPoly (j.comp (val k)) (Poly.ofList r)).eval (ι z) := by
  induction r generalizing a with
  | nil => simp [powers, Model.linearCombination]
  | cons c cs ih =>
    simp [powers, Model.linearCombination, Step.modelPoly_apply, hj, ih, map_add, map_mul]
    ring

private theorem rowHolds_powers (r : List (K R 0)) (c : k) :
    Model.rowHolds k r (powers k c 1 r.length) ↔
      (Step.modelPoly (Model.constantHom k) (Poly.ofList r)).IsRoot c := by
  let e := K.modelConstantsEquiv (R := k) k
  rw [Model.rowHolds, ← (map_eq_zero_iff e e.injective)]
  change e.toRingHom _ = 0 ↔ _
  rw [eval_powers k e.toRingHom (RingHom.id k) (Model.modelConstantsEquiv_C k)]
  simp [IsRoot.def, Model.constantHom, e]

/-- Constant roots are precisely those of the polynomial after interpreting its coefficients. -/
theorem constantRoots_spec [CharZero k] (p : Poly (K R n)) (c : k) :
    (Step.modelPoly (Model.constantHom k) (constantRoots p)).IsRoot c ↔
      (Step.modelPoly (val k) p).IsRoot (Model.C k n c) := by
  rw [constantRoots, Step.sliceRoots_spec]
  let cs := powers k c 1 p.coeffs.length
  have h : (∀ r ∈ rowsOf p.coeffs,
      (Step.modelPoly (Model.constantHom k) (Poly.ofList r)).IsRoot c) ↔
        (∀ r ∈ rowsOf p.coeffs, Model.rowHolds k r cs) := by
    apply forall_congr'
    intro r
    apply forall_congr'
    intro hr
    rw [← rowHolds_powers, length_rowsOf p.coeffs hr]
  rw [h, rowsOf_spec]
  have he := eval_powers k (RingHom.id (M k n)) (Model.C k n) (fun _ => rfl) p.coeffs c 1
  simpa [cs, IsRoot.def] using congrArg (· = 0) he |>.to_iff

/-- A nonzero residue polynomial has only finitely many constant roots. Its computed
constant-root modulus therefore remains nonzero. -/
theorem constantRoots_ne_zero [CharZero k] {p : Poly (K R n)} (hp : p ≠ 0) :
    constantRoots p ≠ 0 := by
  intro hz
  have H : Step.modelPoly (val k) p = 0 := Polynomial.eq_zero_of_infinite_isRoot _ <|
    (Set.infinite_range_of_injective (Model.C k n).injective).mono (by
      rintro x ⟨c, rfl⟩
      exact (constantRoots_spec k p c).mp (by simp [hz]))
  exact hp ((map_eq_zero_iff _
    ((Polynomial.map_injective _ (val_injective (R := R) (n := n) k)).comp
    Poly.equiv.injective)).mp H)

/-- Every root has multiplicity one in the computed modulus when the input is nonzero. -/
theorem constantRoots_squarefree [CharZero k] {p : Poly (K R n)} (hp : p ≠ 0) :
    Squarefree (Step.modelPoly (Model.constantHom k) (constantRoots p)) := by
  let g := (rowsOf p.coeffs).foldl (fun q r => gcd q (Poly.ofList r)) 0
  change Squarefree (Step.modelPoly (Model.constantHom k) (Step.squarefreeParts g).1)
  apply Step.squarefreePart_squarefree
  intro h
  apply constantRoots_ne_zero k hp
  change g / gcd g g.derivative = 0
  simp [h]

/-- The correction coefficient is the negative trace of the residues on its modulus piece,
multiplied by the degree of the logarithm argument in the tower generator. -/
theorem correction_spec (m : Poly (K R 0)) (d : Step.BPoly (K R n)) (hm : 0 < m.natDegree)
    (hs : (Step.modelPoly (Model.constantHom k) m).Splits) :
    Model.constantHom k (correction (m, d)) =
      - (d.natDegree : k) * (Step.modelPoly (Model.constantHom k) m).roots.sum := by
  let p := Step.modelPoly (Model.constantHom k) m
  have hdeg : p.natDegree = m.natDegree := by simp [p, natDegree_map]
  have hl : p.leadingCoeff = Model.constantHom k m.leadingCoeff := by
    simp [p, leadingCoeff_map]
  have nz : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro h
    simp [h] at hdeg
    omega)
  have ht := hs.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  change p.nextCoeff = -p.leadingCoeff * p.roots.sum at ht
  rw [nextCoeff_of_natDegree_pos (hdeg ▸ hm)] at ht
  have hc (i : ℕ) : p.coeff i = Model.constantHom k (m.coeff i) := by simp [p]
  rw [hdeg, hc] at ht
  simp only [correction, map_mul, map_natCast, map_div₀]
  rw [ht, ← hl]
  field_simp
  ring

/-- The Sylvester determinant with the parameter left indeterminate in the coefficients. -/
noncomputable def parameterResultant {F G : Type} [Field F] [DecidableEq F] [Field G]
    (ι : F →+* G) (a d e : Poly F) : G[X] :=
  let j := Polynomial.C.comp ι
  ((Poly.equiv d).map j).resultant ((Poly.equiv a).map j - C X * (Poly.equiv e).map j)

private theorem map_resultant_injective {F G : Type} [CommRing F] [CommRing G] (j : F →+* G)
    (hj : Function.Injective j) (p q : F[X]) :
    j (p.resultant q) = (p.map j).resultant (q.map j) := by
  simp [natDegree_map_eq_of_injective hj]

/-- Splitting the computed fraction in the extra variable recovers precisely the polynomial
Sylvester determinant, including its scalar factor. -/
theorem residuePolynomial_spec (a d e : Poly (K R n)) :
    Step.modelPoly (val k) (residuePolynomial a d e) = parameterResultant (val k) a d e := by
  let P := d.map K.lift
  let Q := a.map K.lift - Poly.C K.gen * e.map K.lift
  let j := (Model.stepEquiv k n).toRingHom.comp (val (R := R) k)
  let i := algebraMap (M k n)[X] (RatFunc (M k n))
  let l := Polynomial.C.comp (val (R := R) (n := n) k)
  have hj : j.comp K.lift = i.comp l := by
    ext x
    simp [j, i, l, Model.stepEquiv_include]
  have hmap (p : Poly (K R n)) :
      (Poly.equiv (p.map K.lift)).map j = ((Poly.equiv p).map l).map i := by
    simp [Polynomial.map_map, hj]
  have hP : (Poly.equiv P).map j = ((Poly.equiv d).map l).map i := hmap _
  have hQ : (Poly.equiv Q).map j =
      (((Poly.equiv a).map l) - C X * ((Poly.equiv e).map l)).map i := by
    have hx : j K.gen = i X := by simp [j, i]
    simp only [Q, map_sub, map_mul, Poly.equiv_C, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, hmap, hx]
  have he : j (Step.resultant P Q) = i (parameterResultant (val k) a d e) := by
    rw [Step.resultant_spec, map_resultant_injective j j.injective, hP, hQ,
      ← map_resultant_injective i (RatFunc.algebraMap_injective _)]
    rfl
  have hs := congrArg Prod.fst (val_split k (Step.resultant P Q))
  change Step.modelPoly (val k) (residuePolynomial a d e) = (j (Step.resultant P Q)).num at hs
  rwa [he, RatFunc.num_algebraMap] at hs

private theorem resultant_root {F : Type} [Field F] {d : F[X]} (hd : d ≠ 0) (g : F[X][X])
    (z : F) : ((d.map C).resultant g).IsRoot z ↔ ¬ IsCoprime d (g.map (evalRingHom z)) := by
  let h := evalRingHom z
  have hd' : (d.map C).map h = d := by
    rw [Polynomial.map_map, show h.comp C = RingHom.id F by ext; simp [h], Polynomial.map_id]
  let q := g.map h
  have hq : q.natDegree ≤ g.natDegree := natDegree_map_le
  have hh := resultant_add_right_deg d q d.natDegree q.natDegree (g.natDegree - q.natDegree) le_rfl
  rw [Nat.add_sub_of_le hq, coeff_natDegree] at hh
  change h ((d.map C).resultant g) = 0 ↔ _
  rw [← resultant_map_map, hd', natDegree_map_eq_of_injective C_injective, hh,
    mul_eq_zero, or_iff_right (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hd)), resultant_eq_zero_iff]
  simp [hd, q, h]

/-- A parameter is a root precisely when its specialized numerator and denominator have a
common nonconstant factor. This also covers a drop in degree at the specialization. -/
theorem parameterResultant_isRoot {F G : Type} [Field F] [DecidableEq F] [Field G]
    (ι : F →+* G) (a d e : Poly F) (hd : d ≠ 0) (z : G) :
    (parameterResultant ι a d e).IsRoot z ↔
      ¬ IsCoprime (Step.modelPoly ι d) (Step.modelPoly ι a - C z * Step.modelPoly ι e) := by
  let l := C.comp ι
  have he (p : Poly F) : ((Poly.equiv p).map l).map (evalRingHom z) = Step.modelPoly ι p := by
    rw [Polynomial.map_map, show (evalRingHom z).comp l = ι by ext; simp [l]]
    rfl
  have h := resultant_root ((map_ne_zero_iff _ ((Polynomial.map_injective _ ι.injective).comp
    Poly.equiv.injective)).mpr hd : Step.modelPoly ι d ≠ 0)
    (((Poly.equiv a).map l) - C X * ((Poly.equiv e).map l)) z
  have hd' : (Step.modelPoly ι d).map C = (Poly.equiv d).map l :=
    Polynomial.map_map _ _ _
  rw [hd'] at h
  simpa only [parameterResultant, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    he, coe_evalRingHom, eval_X] using h

/-- The computable constant-root modulus selects exactly the constant parameters with a
nontrivial logarithmic argument. -/
theorem residue_roots [CharZero k] (a d e : Poly (K R n)) (hd : d ≠ 0) (c : k) :
    (Step.modelPoly (Model.constantHom k) (constantRoots (residuePolynomial a d e))).IsRoot c ↔
      ¬ IsCoprime (Step.modelPoly (val k) d)
        (Step.modelPoly (val k) a - C (Model.C k n c) * Step.modelPoly (val k) e) := by
  rw [constantRoots_spec, residuePolynomial_spec, parameterResultant_isRoot _ _ _ _ hd]

/-- A reduced numerator and denominator give a nonzero residue polynomial. -/
theorem residuePolynomial_ne_zero (a d e : Poly (K R n)) (hd : d ≠ 0)
    (hc : IsCoprime (Step.modelPoly (val k) d) (Step.modelPoly (val k) a)) :
    residuePolynomial a d e ≠ 0 := by
  intro h
  have hr : (parameterResultant (val k) a d e).IsRoot 0 := by
    rw [← residuePolynomial_spec, h, map_zero]
    simp
  apply (parameterResultant_isRoot (val k) a d e hd 0).mp hr
  simpa only [map_zero, zero_mul, sub_zero] using hc

/-- Over an infinite field, some shifted numerator is coprime to the denominator whenever
the derivative polynomial is coprime to it. Each irreducible denominator factor can exclude
at most one scalar. -/
theorem exists_coprime_shift {F : Type} [Field F] [Infinite F] {d e : F[X]} (hd : d ≠ 0)
    (hc : IsCoprime d e) (a : F[X]) : ∃ z : F, IsCoprime d (a - C z * e) := by
  classical
  by_contra! bad
  have h (z : F) : ∃ p ∈ (UniqueFactorizationMonoid.normalizedFactors d).toFinset,
      p ∣ a - C z * e := by
    let b := a - C z * e
    have hg : ¬IsUnit (gcd d b) := fun h => bad z ((gcd_isUnit_iff_isRelPrime.mp h).isCoprime)
    obtain ⟨p,hm,hi,hp⟩ := exists_monic_irreducible_factor (gcd d b) hg
    exact ⟨p, Multiset.mem_toFinset.mpr ((Polynomial.mem_normalizedFactors_iff hd).mpr
      ⟨hi,hm,hp.trans (gcd_dvd_left ..)⟩), hp.trans (gcd_dvd_right ..)⟩
  choose p hp hdiv using h
  let f (z : F) : (UniqueFactorizationMonoid.normalizedFactors d).toFinset := ⟨p z, hp z⟩
  apply not_injective_infinite_finite f
  intro x y hxy
  have eqp : p x = p y := congrArg Subtype.val hxy
  by_contra hne
  have hx := (Polynomial.mem_normalizedFactors_iff hd).mp (Multiset.mem_toFinset.mp (hp x))
  apply hx.1.not_isUnit (hc.isUnit_of_dvd' hx.2.2 _)
  have dv := dvd_sub (eqp ▸ hdiv x : p y ∣ a - C x * e) (hdiv y)
  rw [← eqp] at dv
  have de : p x ∣ C (y-x) * e := by
    convert dv using 1
    rw [map_sub]
    ring
  exact (associated_unit_mul_left e _ (isUnit_C.mpr (sub_ne_zero.mpr (Ne.symm hne)).isUnit))
    |>.dvd_iff_dvd_right.mp de

/-- Coprimality of the denominator and its derivative suffices even if a common denominator
introduced a zero residue in the numerator. -/
theorem residuePolynomial_ne_zero_of_coprime [CharZero k] {a d e : Poly (K R n)} (hd : d ≠ 0)
    (hc : IsCoprime (Step.modelPoly (val k) d) (Step.modelPoly (val k) e)) :
    residuePolynomial a d e ≠ 0 := by
  obtain ⟨z,hz⟩ := exists_coprime_shift (a := Step.modelPoly (val k) a)
    (d := Step.modelPoly (val k) d)
    ((map_ne_zero_iff (Step.modelPoly (val k))
      ((Polynomial.map_injective _ (val_injective (R := R) k)).comp
        Poly.equiv.injective)).mpr hd) hc
  intro he
  apply (parameterResultant_isRoot (val k) a d e hd z).mp _ hz
  rw [← residuePolynomial_spec, he, map_zero]
  simp

/-- The logarithm argument at a residue equals the specialized gcd, evaluated at the newest
tower generator. -/
theorem rootSum_argAt (m : Poly (K R 0)) (d : Step.BPoly (K R n)) (c : k) :
    Model.stepEquiv k n ((rootSum (m, d)).argAt k c) =
      algebraMap (M k n)[X] _ (Step.specialize (Step.atRoot (val k) (Model.C k n c)) d) := by
  let h := Step.atRoot (val (R := R) k) (Model.C k n c)
  let e := Model.stepEquiv k n
  let xb := Model.C k (n + 1) c
  have hc : e xb = RatFunc.C (Model.C k n c) := by
    dsimp only [e, xb]
    rw [← Model.includeVars_C k (n := n) (Nat.le_succ n) c, Model.stepEquiv_include]
  have he (a : Poly (K R n)) :
      e ((Poly.equiv (a.map K.lift)).eval₂ (val k) xb) = RatFunc.C (h a) := by
    change e.toRingHom _ = _
    rw [Poly.equiv_map, eval₂_map, Polynomial.hom_eval₂]
    change Polynomial.eval₂ _ (e xb) _ = _
    rw [hc]
    have ha : h a = (Poly.equiv a).eval₂ (val k) (Model.C k n c) := by
      simp [h, Step.atRoot, eval_map]
    rw [ha]
    rw [Polynomial.hom_eval₂]
    congr 1
    ext t
    simp [e, Model.stepEquiv_include]
  have hx : e (val k (K.gen : K R (n+1))) = RatFunc.X := by simp [e]
  change e ((Poly.equiv (argument d)).eval₂ (val k) xb) = _
  rw [argument]
  generalize hs : d.coeffs = cs
  conv_rhs => rw [← Poly.ofList_coeffs d, hs]
  clear hs
  change _ = algebraMap (M k n)[X] _ (Step.specialize h (Poly.ofList cs))
  have cons (a : Poly (K R n)) (as : List (Poly (K R n))) :
      Step.specialize h (Poly.ofList (a :: as)) =
        C (h a) + X * Step.specialize h (Poly.ofList as) := by
    change (Poly.Raw.toPolynomial (a :: as)).map h =
      C _ + X * (Poly.Raw.toPolynomial as).map h
    simp
  induction cs with
  | nil => simp [Step.specialize]
  | cons a as ih =>
    simp only [List.foldr_cons, map_add, map_mul, Poly.equiv_C, eval₂_add, eval₂_mul,
      eval₂_C, he, hx, ih, cons, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

end SympyProofs.Calculus.Antiderivative.Residue
