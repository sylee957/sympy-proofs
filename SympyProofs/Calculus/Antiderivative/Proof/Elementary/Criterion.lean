module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Laurent

/-! Model-level criterion for a polynomial correction and an elementary lower residual. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial Solve

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

omit [CharZero k] in
private theorem coefficient_op (t : Tower R n) (g : ReducedGen (K R n)) (s : ℕ)
    (q : Polynomial (M k n)) (j : ℕ) :
    (laurentOp k t g s q).coeff j = t.modelD k (q.coeff j) +
      ((j : M k n) - s) * val k ((g.velocity t.D).coeff 1) * q.coeff j +
      ((j+1 : ℕ) : M k n) * val k ((g.velocity t.D).coeff 0) * q.coeff (j+1) := by
  let a := -(s : K R n) * (g.velocity t.D).coeff 1
  change (modelPoly k (1 : Poly (K R n)) * t.polyDerModel k g q +
    modelPoly k (Poly.C a) * q).coeff j = _
  have hc : modelPoly k (Poly.C a) = C (val k a) := by simp [modelPoly]
  rw [show modelPoly k (1 : Poly (K R n)) = 1 by simp [modelPoly], one_mul, hc, coeff_add,
    coeff_C_mul, Solve.coeff_der]
  simp only [a, map_mul, map_neg, map_natCast]
  ring

omit [CharZero k] in
/-- A bounded exponent in a finite sum of monomials specifies each coefficient independently. -/
private theorem coeff_sum_monomial (m : ℕ) (v : ℕ → M k n) (j : ℕ) :
    (∑ i ∈ Finset.range m, monomial i (v i)).coeff j = if j < m then v j else 0 := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]

omit [CharZero k] in
private theorem exp_correction (t : Tower R n) (ht : t.Admissible k) (u : K R n) (s size : ℕ)
    (p : Polynomial (M k n)) (hp : Below size p)
    (he : (t.step (.exp u)).Elementary k (laurentValue k s p)) :
    ∃ q : Polynomial (M k n), Below size q ∧ q.coeff s = 0 ∧
      t.Elementary k (p.coeff s) ∧ p = laurentOp k t (.exp u) s q + monomial s (p.coeff s) := by
  classical
  obtain ⟨hl,hs⟩ := t.elementary_exp_laurent_necessary k u ht p s he
  let y (j : ℕ) := if hj : j = s then 0 else (hs j hj).choose
  let q := ∑ i ∈ Finset.range size, monomial i (y i)
  have hq (j : ℕ) : q.coeff j = if j < size then y j else 0 := coeff_sum_monomial k size y j
  have h₀ : q.coeff s = 0 := by simp [hq,y]
  refine ⟨q, fun j hj => by simp [hq, show ¬ j < size by omega], h₀, hl, ?_⟩
  have hv (i : ℕ) : ((ReducedGen.exp u).velocity t.D).coeff i = if 1 = i then t.D u else 0 := by
    change (Poly.monomial 1 (t.D u)).coeff i = _
    rw [← Poly.coeff_equiv, Poly.equiv_monomial, coeff_monomial_apply]
  ext j
  rw [coeff_add, coefficient_op, hv, hv]
  simp only [ite_true, Nat.one_ne_zero, ite_false, map_zero, mul_zero, zero_mul, add_zero]
  by_cases hj : j = s
  · subst j
    simp [h₀]
  · rw [coeff_monomial_of_ne _ hj, add_zero]
    by_cases hj' : j < size
    · rw [hq, ite_eq_left hj']
      simpa only [y, dite_eq_right hj] using (hs j hj).choose_spec.symm
    · simp [hq, hj', hp j (by omega)]

private theorem prim_correction (t : Tower R n) (ht : t.Admissible k) (b : K R n)
    (hb : (ReducedGen.prim b).Admissible k t) (size : ℕ) (p : Polynomial (M k n))
    (hp : Below size p) (he : (t.step (.prim b)).Elementary k (laurentValue k 0 p)) :
    ∃ (q : Polynomial (M k n)) (r : M k n), Below (size+1) q ∧ q.coeff 0 = 0 ∧
      t.Elementary k r ∧ p = laurentOp k t (.prim b) 0 q + monomial 0 r := by
  by_cases hp0 : p = 0
  · exact ⟨0,0,fun _ _ => coeff_zero _,coeff_zero _,Tower.Elementary.zero k t,by simp [hp0]⟩
  have hpdeg : p.natDegree < size := by
    by_contra hj
    exact hp0 (leadingCoeff_eq_zero.mp ((coeff_natDegree (p := p)).symm.trans (hp _ (by omega))))
  obtain ⟨q,hq,hlo,hcoeff⟩ := (t.elementary_prim_polynomial_iff k b ht hb p).mp (by
    simpa [laurentValue] using he)
  let z := q - C (q.coeff 0)
  have hz₀ : z.coeff 0 = 0 := by simp [z]
  have hz (j : ℕ) : z.coeff (j+1) = q.coeff (j+1) := by simp [z]
  have hlate (j : ℕ) (hj : p.natDegree < j) : q.coeff (j+1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨z,_,?_,hz₀,hlo,?_⟩
  · rintro (_ | j) hj
    · omega
    · rw [hz]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have hv (j : ℕ) : ((ReducedGen.prim b).velocity t.D).coeff j = if j = 0 then b else 0 := by
      simp [ReducedGen.velocity, Gen.velocity, ← Poly.coeff_equiv, coeff_C]
    ext j
    rw [coeff_add, coefficient_op, hv, hv]
    simp only [Nat.one_ne_zero, ite_false, ite_true, map_zero, mul_zero, zero_mul, add_zero]
    cases j with
    | zero => simp [hz₀, hz]
    | succ j =>
      simp only [coeff_monomial_apply, Nat.zero_ne_add_one, ite_false, hz, add_zero]
      by_cases hj : j ≤ p.natDegree
      · exact (hcoeff j hj).symm
      · rw [hlate j (by omega), hlate (j+1) (by omega), map_zero, mul_zero, add_zero]
        exact coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j+1)

/-- A Laurent input is elementary exactly when a bounded polynomial correction leaves an
elementary lower constant coefficient. Primitive corrections may use one extra power. -/
theorem elementary_iff_correction (t : Tower R n) (g : ReducedGen (K R n))
    (ht : t.Admissible k)
    (hg : g.Admissible k t) (s size : ℕ) (hs : LawfulShift g s) (p : Polynomial (M k n))
    (hp : Below size p) :
    (t.step g).Elementary k (laurentValue k s p) ↔
      ∃ (q : Polynomial (M k n)) (r : M k n),
        Below (degreeCutoff g size) q ∧ q.coeff s = 0 ∧
        t.Elementary k r ∧ p = laurentOp k t g s q + monomial s r := by
  constructor
  · intro he
    cases g with
    | prim b =>
      obtain rfl : s = 0 := hs
      exact prim_correction k t ht b hg size p hp he
    | exp u =>
      obtain ⟨q,hq,h₀,hl,he⟩ := exp_correction k t ht u s size p hp he
      exact ⟨q,p.coeff s,hq,h₀,hl,he⟩
  · rintro ⟨q,r,_,_,hl,he⟩
    exact elementary_of_correction k t g s hs p q r hl he

end SympyProofs.Calculus.Antiderivative.Elementary
