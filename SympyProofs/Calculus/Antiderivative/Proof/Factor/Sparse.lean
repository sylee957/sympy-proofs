module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Clear
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Kronecker

/-! Polynomial semantics and partial-degree bounds for the cleared sparse representation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Interpret a sparse coefficient list over the constant field as a multivariate polynomial. -/
noncomputable def sparsePolynomial (k : ℕ) (ts : List (List ℕ × F)) : MvPolynomial (Fin k) F :=
  (ts.map fun (m, a) => MvPolynomial.monomial (Mono.exponents k m) a).sum

private theorem exponents_of_length (m : List ℕ) {k : ℕ} (hm : m.length = k) :
    List.ofFn (Mono.exponents k m) = m := by
  apply List.ext_getElem (by simp [hm])
  intro i _ hi
  simp [Mono.exponents_apply, Poly.Raw.coeff, List.getD_eq_getElem?_getD, hi]

omit [Field F] [DecidableEq F] in
private theorem max_exp (i : ℕ) (ts : List (List ℕ × F)) (a : ℕ) :
    let mx := ts.foldl (fun b t => max b (t.1[i]?.getD 0 + 1)) a
    a ≤ mx ∧ ∀ t ∈ ts, t.1[i]?.getD 0 < mx := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨ha, h⟩ := ih (max a (t.1[i]?.getD 0 + 1))
    refine ⟨(le_max_left ..).trans ha, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right ..).trans ha)
    · exact h _ hs

omit [DecidableEq F] in
private theorem bounds_of_terms {k : ℕ} (bs : List ℕ) (ts : List (List ℕ × F)) (i : Fin k)
    (hp : 0 < bs.getD i.val 0) (h : ∀ t ∈ ts, t.1.getD i.val 0 < bs.getD i.val 0) :
    (sparsePolynomial k ts).degreeOf i < bs.getD i.val 0 := by
  induction ts with
  | nil => simpa [sparsePolynomial] using hp
  | cons t ts ih =>
    obtain ⟨m, a⟩ := t
    change (MvPolynomial.monomial (Mono.exponents k m) a + sparsePolynomial k ts).degreeOf i < _
    apply lt_of_le_of_lt (MvPolynomial.degreeOf_add_le ..) (max_lt _ _)
    · by_cases ha : a = 0
      · simpa [ha] using hp
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ ha]
        exact h _ List.mem_cons_self
    · exact ih (fun t ht => h _ (List.mem_cons_of_mem _ ht))

omit [DecidableEq F] in
/-- The chosen radices strictly dominate every partial degree. -/
theorem sparse_bounds (ts : List (List ℕ × F)) (k : ℕ) (i : Fin k) :
    (sparsePolynomial k ts).degreeOf i < (radices k ts).getD i.val 0 := by
  have hm := max_exp i.val ts 1
  have hbase : (radices k ts).getD i.val 0 =
      ts.foldl (fun b t => max b (t.1[i.val]?.getD 0 + 1)) 1 := by
    simp [radices, List.getD_eq_getElem?_getD, i.isLt]
  apply bounds_of_terms
  · rw [hbase]; exact hm.1
  · intro t ht
    rw [hbase, List.getD_eq_getElem?_getD]
    exact hm.2 _ ht

private theorem substitute_fold (bs : List ℕ) (ts : List (List ℕ × F)) (p : Poly F) :
    ts.foldl (fun q t => q + Poly.monomial (encode bs t.1) t.2) p =
      p + (ts.map fun t => Poly.monomial (encode bs t.1) t.2).sum := by
  induction ts generalizing p with
  | nil => simp
  | cons t ts ih => simp [ih, add_assoc]

/-- Substitution of the sparse input computes the polynomial ring homomorphism. -/
theorem substitute_eq (bs : List ℕ) {k : ℕ} (hbs : bs.length = k) (ts : List (List ℕ × F))
    (hl : ∀ t ∈ ts, t.1.length = k) :
    substitute bs ts = substituteHom bs k (sparsePolynomial k ts) := by
  rw [substitute, substitute_fold, zero_add, sparsePolynomial, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨m, c⟩ h
  simp [substituteHom_monomial bs hbs, exponents_of_length _ (hl _ h)]

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- The sparse polynomial evaluated at the original variables has the sparse term value. -/
theorem restore_eq {n k : ℕ} (f : K R n →+* G) (vs : List (Poly G))
    (ts : List (List ℕ × K R n)) (hl : ∀ t ∈ ts, t.1.length = k) :
    restoreHom f vs k (sparsePolynomial k ts) = termsValue f vs ts := by
  rw [sparsePolynomial, map_list_sum, List.map_map, termsValue]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨m, c⟩ h
  simp [restoreHom_monomial, exponents_of_length _ (hl _ h)]

/-- Clearing prepends exactly one digit per lower variable, to every nonzero term. -/
theorem clearTerms_width {n : ℕ} (ts : List (List ℕ × K R n)) (width : ℕ)
    (h : ∀ t ∈ ts, t.1.length = width) : ∀ t ∈ clearTerms ts, t.1.length = n + width := by
  induction n generalizing width with
  | zero => simpa [clearTerms] using h
  | succ n ih =>
    rw [clearTerms]
    have he : n + 1 + width = n + (width + 1) := by omega
    rw [he]
    apply ih
    intro t ht
    obtain ⟨⟨⟨m, c⟩, p⟩, hz, hm⟩ := List.mem_flatMap.mp ht
    obtain ⟨⟨a, i⟩, _, ha⟩ := List.mem_filterMap.mp hm
    change (if a = 0 then none else some (i :: m, a)) = some t at ha
    split at ha
    · contradiction
    · cases ha
      simp [h _ (List.of_mem_zip hz).1]

end SympyProofs.Calculus.Antiderivative.Factor
