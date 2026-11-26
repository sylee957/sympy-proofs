module

public import SympyProofs.Calculus.Antiderivative.Program.Step.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Hermite

/-! The constant roots of the coefficient slices and specialization of modular remainders. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Step

open Polynomial
open scoped Polynomial

variable {C k : Type} [Field C] [DecidableEq C] [Field k]

/-- Mapping the coefficients of the executable univariate representation into a model field. -/
noncomputable def modelPoly (ι : C →+* k) : Poly C →+* k[X] :=
  (Polynomial.mapRingHom ι).comp Poly.equiv.toRingHom

@[simp] theorem modelPoly_apply (ι : C →+* k) (p : Poly C) :
    modelPoly ι p = (Poly.equiv p).map ι := rfl

/-- A homomorphism kills a polynomial gcd exactly when it kills both polynomials. -/
theorem map_gcd_eq_zero_iff (h : Poly C →+* k) (a b : Poly C) :
    h (gcd a b) = 0 ↔ h a = 0 ∧ h b = 0 := by
  constructor
  · intro hz
    constructor
    · exact zero_dvd_iff.mp (hz ▸ map_dvd h (gcd_dvd_left a b))
    · exact zero_dvd_iff.mp (hz ▸ map_dvd h (gcd_dvd_right a b))
  · rintro ⟨ha, hb⟩
    rw [← bezout_spec a b, map_add, map_mul, map_mul, ha, hb, zero_mul, zero_mul, zero_add]

private theorem gcdRows_zero (h : Poly C →+* k) (rows : List (List C)) (p : Poly C) :
    h (rows.foldl (fun g r => gcd g (Poly.ofList r)) p) = 0 ↔
      h p = 0 ∧ ∀ r ∈ rows, h (Poly.ofList r) = 0 := by
  induction rows generalizing p with
  | nil => simp
  | cons r rs ih => simp [ih, map_gcd_eq_zero_iff, and_assoc]

/-- The squarefree part has precisely the original roots after any extension of constants. -/
theorem squarefreePart_roots [CharZero k] (ι : C →+* k) (g : Poly C) (z : k) :
    (modelPoly ι (squarefreeParts g).1).IsRoot z ↔ (modelPoly ι g).IsRoot z := by
  by_cases hg : g = 0
  · simp [hg, squarefreeParts]
  have inj : Function.Injective (modelPoly ι) :=
    (map_injective _ ι.injective).comp Poly.equiv.injective
  have nz := (map_ne_zero_iff _ inj).mpr hg
  have h := congrArg (modelPoly ι) (squarefreeParts_mul hg).symm
  rw [map_mul] at h
  have dvd : modelPoly ι (squarefreeParts g).2 ∣ (modelPoly ι g).derivative := by
    simpa [squarefreeParts, derivative_map] using
      map_dvd (modelPoly ι) (gcd_dvd_right g g.derivative)
  rw [← dvd_iff_isRoot, ← dvd_iff_isRoot]
  exact ⟨fun hq => hq.trans ⟨_, h.trans (mul_comm _ _)⟩,
    Extension.Hermite.prime_dvd_of_gcd nz h dvd (prime_X_sub_C z)⟩

/-- The roots of the computed squarefree modulus are the simultaneous roots of the slices. -/
theorem sliceRoots_spec [CharZero k] (ι : C →+* k) (rows : List (List C)) (z : k) :
    (modelPoly ι (sliceRoots rows)).IsRoot z ↔
      ∀ r ∈ rows, (modelPoly ι (Poly.ofList r)).IsRoot z := by
  let g := rows.foldl (fun q r => gcd q (Poly.ofList r)) 0
  change (modelPoly ι (squarefreeParts g).1).IsRoot z ↔ _
  rw [squarefreePart_roots]
  let h := (evalRingHom z).comp (modelPoly ι)
  change h g = 0 ↔ ∀ r ∈ rows, h (Poly.ofList r) = 0
  simpa [g] using gcdRows_zero h rows 0

/-- The squarefree factor of a nonzero polynomial remains squarefree in any model field. -/
theorem squarefreePart_squarefree (ι : C →+* k) {g : Poly C} (hg : g ≠ 0) :
    Squarefree (modelPoly ι (squarefreeParts g).1) := by
  have inj : Function.Injective (modelPoly ι) :=
    (map_injective _ ι.injective).comp Poly.equiv.injective
  have h := congrArg (modelPoly ι) (squarefreeParts_mul hg).symm
  rw [map_mul] at h
  apply Extension.Hermite.squarefree_of_gcd (a := modelPoly ι (bezout g g.derivative).1)
    (b := modelPoly ι (bezout g g.derivative).2) ((map_ne_zero_iff _ inj).mpr hg) h
  have hb := congrArg (modelPoly ι) (bezout_spec g g.derivative)
  simpa [squarefreeParts, mul_comm, derivative_map] using hb

/-- Evaluating a coefficient modulo a polynomial in the kernel does not change its image. -/
theorem map_mod_of_zero (h : Poly C →+* k) {m : Poly C} (hm : h m = 0) (a : Poly C) :
    h (a % m) = h a := by
  simpa [hm] using congrArg h (EuclideanDomain.mod_add_div a m)

/-- Specialize the residue parameter, leaving the tower generator as an indeterminate. -/
noncomputable def specialize (h : Poly C →+* k) : BPoly C →+* k[X] :=
  (Polynomial.mapRingHom h).comp Poly.equiv.toRingHom

@[simp] theorem coeff_specialize (h : Poly C →+* k) (a : BPoly C) (i : ℕ) :
    (specialize h a).coeff i = h (a.coeff i) := by simp [specialize]

theorem specialize_reduceMod (h : Poly C →+* k) {m : Poly C} (hm : h m = 0) (a : BPoly C) :
    specialize h (reduceMod m a) = specialize h a := by
  ext i
  rw [coeff_specialize, coeff_specialize, reduceMod,
    Poly.coeff_map (· % m) (EuclideanDomain.zero_mod _),
    map_mod_of_zero h hm]

/-- Each modular reduction step preserves the residue class modulo the specialized divisor. -/
theorem specialize_remainder_congr (h : Poly C →+* k) {m : Poly C} (hm : h m = 0)
    (b : BPoly C) (fuel : ℕ) (a : BPoly C) :
    specialize h (remainderMonic m b fuel a) % specialize h b =
      specialize h a % specialize h b := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    rw [remainderMonic]
    split
    · rfl
    · rw [ih, specialize_reduceMod h hm, map_sub, map_mul]
      apply mod_eq_of_dvd_sub
      rw [sub_sub_cancel_left]
      exact dvd_neg.mpr (dvd_mul_left _ _)

/-- Coefficient reduction cannot increase the degree in the tower generator. -/
theorem degree_reduceMod_le (m : Poly C) (a : BPoly C) :
    (Poly.equiv (reduceMod m a)).degree ≤ (Poly.equiv a).degree := by
  rw [degree_le_iff_coeff_zero]
  intro i hi
  rw [Poly.coeff_equiv, reduceMod, Poly.coeff_map (· % m) (EuclideanDomain.zero_mod _),
    ← Poly.coeff_equiv, coeff_eq_zero_of_degree_lt hi, EuclideanDomain.zero_mod]

/-- The modular long division gives zero or a result of degree strictly below the divisor. -/
theorem remainderMonic_degree (m : Poly C) {b : BPoly C} (hb : (Poly.equiv b).Monic)
    (fuel : ℕ) (a : BPoly C) (ha : a = 0 ∨ a.natDegree < fuel) :
    (Poly.equiv (remainderMonic m b fuel a)).degree < (Poly.equiv b).degree := by
  have hz : (Poly.equiv (0 : BPoly C)).degree < (Poly.equiv b).degree := by
    simpa using (degree_ne_bot.mpr hb.ne_zero).bot_lt
  induction fuel generalizing a with
  | zero =>
    rcases ha with rfl | h
    · exact hz
    · omega
  | succ fuel ih =>
    rw [remainderMonic]
    split
    · rename_i h
      have h' : a = 0 ∨ a.natDegree < b.natDegree := by simpa using h
      rcases h' with rfl | hd
      · exact hz
      · exact degree_lt_degree (by simpa using hd)
    · rename_i h
      have h' : a ≠ 0 ∧ b.natDegree ≤ a.natDegree := by simpa using h
      have hA : Poly.equiv a ≠ 0 := (map_ne_zero_iff _ Poly.equiv.injective).mpr h'.1
      have hl : (Poly.equiv b).degree ≤ (Poly.equiv a).degree := by
        rw [degree_eq_natDegree hA, degree_eq_natDegree hb.ne_zero]
        simpa using h'.2
      have hd := div_wf_lemma ⟨hl, hA⟩ hb
      let q := Poly.monomial (a.natDegree - b.natDegree) a.leadingCoeff
      let r := reduceMod m (a - q * b)
      have hr : (Poly.equiv r).degree < (Poly.equiv a).degree := by
        apply lt_of_le_of_lt (degree_reduceMod_le m _)
        simpa only [map_sub, map_mul, q, Poly.equiv_monomial, ← C_mul_X_pow_eq_monomial,
          Poly.leadingCoeff_equiv, Poly.natDegree_equiv, mul_comm (Poly.equiv b)] using hd
      apply ih
      by_cases he : r = 0
      · exact Or.inl he
      · have hlt := natDegree_lt_natDegree ((map_ne_zero_iff _ Poly.equiv.injective).mpr he) hr
        simp only [Poly.natDegree_equiv] at hlt
        exact Or.inr (lt_of_lt_of_le hlt (Nat.le_of_lt_succ (ha.resolve_left h'.1)))

/-- Modular long division specializes to ordinary Euclidean remainder on every root of the
modulus when its divisor has already been made monic. -/
theorem specialize_remainderMonic (h : Poly C →+* k) {m : Poly C} (hm : h m = 0)
    {b : BPoly C} (hb : (Poly.equiv b).Monic) (a : BPoly C) :
    specialize h (remainderMonic m b (a.natDegree + 1) a) =
      specialize h a % specialize h b := by
  let r := remainderMonic m b (a.natDegree + 1) a
  have hr := remainderMonic_degree m hb (a.natDegree + 1) a (Or.inr (Nat.lt_succ_self _))
  have hdeg : (specialize h r).degree < (specialize h b).degree := by
    change ((Poly.equiv r).map h).degree < ((Poly.equiv b).map h).degree
    rw [hb.degree_map]
    exact degree_map_le.trans_lt hr
  have hn : specialize h b ≠ 0 := (hb.map h).ne_zero
  exact ((Polynomial.mod_eq_self_iff hn).mpr hdeg).symm.trans
    (specialize_remainder_congr h hm b _ a)

/-- Specializing the symbolic parameter to a point of a coefficient extension. -/
noncomputable def atRoot (ι : C →+* k) (z : k) : Poly C →+* k :=
  (evalRingHom z).comp (modelPoly ι)

@[simp] theorem atRoot_C (ι : C →+* k) (z : k) (a : C) : atRoot ι z (Poly.C a) = ι a := by
  simp [atRoot]

@[simp] theorem atRoot_X (ι : C →+* k) (z : k) : atRoot ι z Poly.X = z := by simp [atRoot]

@[simp] theorem specialize_independent (ι : C →+* k) (z : k) (a : Poly C) :
    specialize (atRoot ι z) (independent a) = modelPoly ι a := by
  ext i
  simp [independent, Poly.coeff_map _ Poly.C_zero]

@[simp] theorem specialize_shifted (ι : C →+* k) (z : k) (a e : Poly C) :
    specialize (atRoot ι z) (shifted a e) = modelPoly ι a - Polynomial.C z * modelPoly ι e := by
  simp [shifted, show specialize (atRoot ι z) (Poly.C Poly.X) = Polynomial.C z by
    simp [specialize]]

/-- Multiplying by the Bézout inverse of the leading coefficient before coefficient reduction
makes the entire bivariate polynomial monic over the original coefficient ring. -/
theorem monic_reduce_bezout {m : Poly C} (hm : 0 < m.natDegree) (p : BPoly C)
    (hg : gcd p.leadingCoeff m = 1) :
    (Poly.equiv (reduceMod m (Poly.C (bezout p.leadingCoeff m).1 * p))).Monic := by
  let u := (bezout p.leadingCoeff m).1
  let r := reduceMod m (Poly.C u * p)
  have hle : (Poly.equiv r).natDegree ≤ p.natDegree := by
    apply (natDegree_le_natDegree (degree_reduceMod_le m _)).trans
    simpa using natDegree_C_mul_le u (Poly.equiv p)
  have hbez := bezout_spec p.leadingCoeff m
  rw [hg] at hbez
  have hm' : Poly.equiv m ≠ 0 := by
    intro h
    have h₀ := congrArg Polynomial.natDegree h
    simp at h₀
    omega
  have hmod : (u * p.leadingCoeff) % m = 1 := by
    apply Poly.equiv.injective
    rw [Poly.equiv_mod, map_one]
    have he : (Poly.equiv (u * p.leadingCoeff)) % Poly.equiv m = 1 % Poly.equiv m := by
      apply mod_eq_of_dvd_sub
      refine ⟨-Poly.equiv (bezout p.leadingCoeff m).2, ?_⟩
      rw [← map_one Poly.equiv, ← hbez]
      simp only [u, map_mul, map_add]
      ring
    exact he.trans ((mod_eq_self_iff hm').mpr (degree_lt_degree (by simpa using hm)))
  apply monic_of_natDegree_le_of_coeff_eq_one _ hle
  dsimp only [r]
  rw [Poly.coeff_equiv, reduceMod, Poly.coeff_map (· % m) (EuclideanDomain.zero_mod _),
    ← Poly.coeff_equiv, map_mul, Poly.equiv_C, coeff_C_mul, Poly.coeff_equiv,
    Poly.coeff_natDegree]
  exact hmod

/-- The product of the constant moduli is preserved by every leading-coefficient split. -/
theorem monicPieces_product {F : Type} [Field F] [DecidableEq F]
    (embed : C → F) (roots : Poly F → Poly C) (fuel : ℕ) (m : Poly C) (p : BPoly F) :
    ((monicPieces embed roots fuel m p).map Prod.fst).prod = m := by
  induction fuel generalizing m p with
  | zero => simp [monicPieces]
  | succ fuel ih =>
    rw [monicPieces]
    split
    · simp
    · dsimp only
      split
      · simp
      · simp only [List.map_append, List.prod_append, ih]
        let g := gcd m (roots (reduceMod (m.map embed) p).leadingCoeff)
        change g * (m / g) = m
        by_cases hg : g = 0
        · obtain rfl : m = 0 := zero_dvd_iff.mp (hg ▸ gcd_dvd_left m _ : 0 ∣ m)
          simp
        · exact EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)

/-- The complete Euclidean recursion preserves the product of the partition moduli. -/
theorem gcdAtRoots_product {F : Type} [Field F] [DecidableEq F]
    (embed : C → F) (roots : Poly F → Poly C) (fuel : ℕ) (m : Poly C) (a b : BPoly F) :
    ((gcdAtRoots embed roots fuel m a b).map Prod.fst).prod = m := by
  induction fuel generalizing m a b with
  | zero => exact monicPieces_product ..
  | succ fuel ih =>
    rw [gcdAtRoots]
    have hf (u : Poly C × BPoly F) :
        ((if u.2 = 0 then monicPieces embed roots (u.1.natDegree+1) u.1 a
        else gcdAtRoots embed roots fuel u.1 u.2 (remainderMonic (u.1.map embed) u.2
          ((reduceMod (u.1.map embed) a).natDegree+1) (reduceMod (u.1.map embed) a))).map
            Prod.fst).prod = u.1 := by
      split
      · exact monicPieces_product ..
      · exact ih ..
    conv_rhs => rw [← monicPieces_product embed roots (m.natDegree+1) m b]
    generalize monicPieces embed roots (m.natDegree+1) m b = ps
    induction ps with
    | nil => rfl
    | cons p ps ih' =>
      rcases p with ⟨u,d⟩
      simp only [List.flatMap_cons, List.map_append, List.prod_append, ih', List.map_cons,
        List.prod_cons]
      rw [hf (u, d)]

end SympyProofs.Calculus.Antiderivative.Step
