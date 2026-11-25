module

public import SympyProofs.Calculus.Risch.Spec.Derivation

/-! The symbolic derivative of a term denotes the derivative of the element the term
denotes, in the field of the tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

noncomputable local instance intAlgebraDerivative {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

namespace Tower

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-- The symbolic derivative is correct once it is correct on the generators. -/
theorem der_value_of_gens (t : Tower n)
    (hg : ∀ i, t.der k (gens k n i) = Term.value k (t.vel i)) (e : Term n) :
    t.der k (Term.value k e) = Term.value k (t.D e) := by
  induction e with
  | const q =>
    change t.der k (q : K k n) = ((0 : ℚ) : K k n)
    rw [Rat.cast_def]
    simp [Derivation.leibniz_div]
  | gen i => exact hg i
  | neg a ha =>
    change t.der k (-(Term.value k a)) = -(Term.value k (t.D a))
    rw [map_neg, ha]
  | add a b ha hb =>
    change t.der k (Term.value k a + Term.value k b) =
      Term.value k (t.D a) + Term.value k (t.D b)
    rw [map_add, ha, hb]
  | sub a b ha hb =>
    change t.der k (Term.value k a - Term.value k b) =
      Term.value k (t.D a) - Term.value k (t.D b)
    rw [map_sub, ha, hb]
  | mul a b ha hb =>
    change t.der k (Term.value k a * Term.value k b) =
      Term.value k (t.D a) * Term.value k b + Term.value k a * Term.value k (t.D b)
    rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul]
    ring
  | div a b ha hb =>
    change t.der k (Term.value k a / Term.value k b) =
      (Term.value k (t.D a) * Term.value k b - Term.value k a * Term.value k (t.D b)) /
        (Term.value k b * Term.value k b)
    rw [Derivation.leibniz_div, ha, hb]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring

/-- The derivative of each generator is denoted by its term. -/
theorem der_gens (t : Tower n) : ∀ i, t.der k (gens k n i) = Term.value k (t.vel i) := by
  induction t with
  | const => exact fun i => i.elim0
  | prim t b ih =>
    apply Fin.lastCases
    · simp only [gens, vel, Fin.lastCases_last]
      rw [der_prim_X, Term.value_weaken]
    · intro i
      simp only [gens, vel, Fin.lastCases_castSucc]
      rw [der_prim_C, ih, Term.value_weaken]
  | exp t u ih =>
    apply Fin.lastCases
    · simp only [gens, vel, Fin.lastCases_last]
      change _ = gens k _ (Fin.last _) * Term.value k (u.deriv t.vel).weaken
      simp only [gens, Fin.lastCases_last, Term.value_weaken]
      rw [der_exp_X, der_value_of_gens t ih u, mul_comm]
      rfl
    · intro i
      simp only [gens, vel, Fin.lastCases_castSucc]
      rw [der_exp_C, ih, Term.value_weaken]

/-- The symbolic derivative of a term denotes the derivative of its value. -/
theorem der_value (t : Tower n) (e : Term n) :
    t.der k (Term.value k e) = Term.value k (t.D e) :=
  der_value_of_gens t t.der_gens e

end Tower

end SympyProofs.Calculus.Risch
