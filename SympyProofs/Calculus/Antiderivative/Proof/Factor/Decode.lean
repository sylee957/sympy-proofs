module

public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Tower

/-! The decoder is additive and commutes with multiplication by constant coefficients. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]
variable (f : F →+* G) (vs : List (Poly G)) (bs : List ℕ)

private theorem decode_fold (ts : List (F × ℕ)) (r : Poly G) :
    ts.foldl (fun r (a, i) => if a = 0 then r else r + decodeTerm f vs bs i a) r =
      r + (ts.map fun (a, i) => decodeTerm f vs bs i a).sum := by
  induction ts generalizing r with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨a, i⟩ := t
    rw [List.foldl_cons, ih]
    by_cases ha : a = 0 <;> simp [ha, decodeTerm, add_assoc]

omit [DecidableEq G] in
private theorem zipIdx_weights (p : Poly F) (w : ℕ → F → Poly G) :
    (p.coeffs.zipIdx.map fun (a, i) => w i a) =
      (List.range p.coeffs.length).map fun i => w i (p.coeff i) := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have h : i < p.coeffs.length := by simpa using hi
  simp [List.getElem_zipIdx, Poly.coeff_eq_getD_coeffs, List.getD_eq_getElem?_getD, h]

/-- Decoding the coefficient array is linear summation of its decoded monomials. -/
theorem decode_eq_sum (q : Poly F) :
    decode f vs bs q = (Poly.equiv q).sum (decodeTerm f vs bs) := by
  rw [decode, decode_fold, zero_add, zipIdx_weights]
  by_cases h : q = 0
  · simp [h]
  have hlen : q.natDegree < q.coeffs.length := by
    rw [Poly.natDegree_eq]
    have ne := mt Poly.coeffs_eq_nil.mp h
    have hp := List.length_pos_of_ne_nil ne
    omega
  rw [Polynomial.sum_over_range' _ (by simp [decodeTerm]) q.coeffs.length (by simpa using hlen),
    ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  simp

@[simp] theorem decode_add (a b : Poly F) :
    decode f vs bs (a+b) = decode f vs bs a + decode f vs bs b := by
  rw [decode_eq_sum, decode_eq_sum, decode_eq_sum, map_add]
  exact Polynomial.sum_add_index _ _ _ (by simp [decodeTerm])
    (by simp [decodeTerm, Poly.C_add, add_mul])

@[simp] theorem decode_monomial (i : ℕ) (a : F) :
    decode f vs bs (Poly.monomial i a) = decodeTerm f vs bs i a := by
  rw [decode_eq_sum, Poly.equiv_monomial, Polynomial.sum_monomial_index]
  simp [decodeTerm]

/-- Since decoding is linear, normalizing an encoded divisor scales its decoded coefficients
by the inverse of its original leading coefficient. -/
theorem decode_C_mul (a : F) (q : Poly F) :
    decode f vs bs (Poly.C a * q) = Poly.C (f a) * decode f vs bs q := by
  induction h : Poly.equiv q using Polynomial.induction_on' generalizing q with
  | add P Q ihP ihQ =>
    let p : Poly F := Poly.equiv.symm P
    let r : Poly F := Poly.equiv.symm Q
    have split : q = p + r := Poly.equiv.injective (by simp [p, r, h])
    rw [split, mul_add, decode_add, ihP p (by simp [p]), ihQ r (by simp [r]), decode_add, mul_add]
  | monomial i b =>
    have eq : q = Poly.monomial i b := Poly.equiv.injective (by simp [h])
    have mul : Poly.C a * Poly.monomial i b = Poly.monomial i (a*b) :=
      Poly.equiv.injective (by simp [Polynomial.C_mul_monomial])
    simp [eq, mul, decodeTerm, Poly.C_mul, mul_assoc]

end SympyProofs.Calculus.Antiderivative.Factor
