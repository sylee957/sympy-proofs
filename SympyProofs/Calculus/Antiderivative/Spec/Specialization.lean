module

public import SympyProofs.Calculus.Antiderivative.Spec.Level

/-! Evaluation of a rational function at a point where it admits a regular fraction. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Model

variable {k : Type} [Field k] {n : ℕ} (p : Fin n → k)

/-- A rational function takes the value `c` if it has a presentation with nonvanishing
denominator whose numerator evaluates to `c` times that denominator. -/
def HasValue (x : M k n) (c : k) : Prop :=
  ∃ a b : MvPolynomial (Fin n) k, polynomial k a = x * polynomial k b ∧
    MvPolynomial.eval p b ≠ 0 ∧ MvPolynomial.eval p a = c * MvPolynomial.eval p b

namespace HasValue

variable {p} {x y : M k n} {c d : k}

/-- Two fractions representing the same element have the same value at every common point. -/
theorem unique (h : HasValue p x c) (h' : HasValue p x d) : c = d := by
  obtain ⟨a, b, hx, hb, ha⟩ := h
  obtain ⟨u, v, hy, hv, hu⟩ := h'
  have eqn : a * v = u * b := by
    apply IsFractionRing.injective (MvPolynomial (Fin n) k) (M k n)
    change polynomial k (a * v) = polynomial k (u * b)
    simp only [polynomial, map_mul] at hx hy ⊢
    rw [hx, hy]
    ring
  have e := congrArg (MvPolynomial.eval p) eqn
  simp only [map_mul, ha, hu] at e
  apply mul_right_cancel₀ (mul_ne_zero hb hv)
  linear_combination e

protected theorem polynomial (a : MvPolynomial (Fin n) k) :
    HasValue p (polynomial k a) (MvPolynomial.eval p a) :=
  ⟨a, 1, by simp, by simp, by simp⟩

protected theorem C (a : k) : HasValue p (C k n a) a := by
  change HasValue p (Model.polynomial k (MvPolynomial.C a)) a
  simpa only [MvPolynomial.eval_C] using HasValue.polynomial (p := p) (MvPolynomial.C a)

protected theorem zero : HasValue p (0 : M k n) 0 := by simpa using HasValue.C (p := p) 0

protected theorem add (h : HasValue p x c) (g : HasValue p y d) : HasValue p (x+y) (c+d) := by
  obtain ⟨a, b, hx, hb, ha⟩ := h
  obtain ⟨u, v, hy, hv, hu⟩ := g
  refine ⟨a*v + u*b, b*v, ?_, by simpa using mul_ne_zero hb hv, ?_⟩
  · simp only [map_add, map_mul, hx, hy]
    ring
  · simp only [map_add, map_mul, ha, hu]
    ring

protected theorem mul (h : HasValue p x c) (g : HasValue p y d) : HasValue p (x*y) (c*d) := by
  obtain ⟨a, b, hx, hb, ha⟩ := h
  obtain ⟨u, v, hy, hv, hu⟩ := g
  refine ⟨a*u, b*v, ?_, by simpa using mul_ne_zero hb hv, ?_⟩
  · simp only [map_mul, hx, hy]
    ring
  · simp only [map_mul, ha, hu]
    ring

protected theorem neg (h : HasValue p x c) : HasValue p (-x) (-c) := by
  obtain ⟨a, b, hx, hb, ha⟩ := h
  exact ⟨-a, b, by simp [hx], hb, by simp [ha]⟩

protected theorem sub (h : HasValue p x c) (g : HasValue p y d) : HasValue p (x-y) (c-d) := by
  simpa only [sub_eq_add_neg] using h.add g.neg

protected theorem inv (h : HasValue p x c) (hc : c ≠ 0) : HasValue p x⁻¹ c⁻¹ := by
  obtain ⟨a, b, hx, hb, ha⟩ := h
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_mul] at hx
    have hn : a = 0 := (IsFractionRing.injective _ (M k n)) (hx.trans (map_zero _).symm)
    simp [hn, hc, hb] at ha
  refine ⟨b, a, by rw [hx, inv_mul_cancel_left₀ hx0], by rw [ha]; exact mul_ne_zero hc hb, ?_⟩
  rw [ha, inv_mul_cancel_left₀ hc]

protected theorem div (h : HasValue p x c) (g : HasValue p y d) (hd : d ≠ 0) :
    HasValue p (x/y) (c/d) := by simpa only [div_eq_mul_inv] using h.mul (g.inv hd)

end HasValue

/-- A fraction is regular at a point if it admits a denominator that does not vanish there. -/
def RegularAt (x : M k n) : Prop := ∃ c, HasValue p x c

/-- The value of a fraction at a regular point, with zero as the default at a pole. -/
noncomputable def evalAt (x : M k n) : k := by
  classical
  exact if h : RegularAt p x then h.choose else 0

theorem HasValue.evalAt {p : Fin n → k} {x : M k n} {c : k} (h : HasValue p x c) :
    evalAt p x = c := by
  have hr : RegularAt p x := ⟨c, h⟩
  classical
  simpa only [Model.evalAt, dite_eq_left_of_eq_true (eq_true hr)] using hr.choose_spec.unique h

theorem RegularAt.hasValue {p : Fin n → k} {x : M k n} (h : RegularAt p x) :
    HasValue p x (evalAt p x) := by
  obtain ⟨c,h⟩ := h
  rw [h.evalAt]
  exact h

end SympyProofs.Calculus.Antiderivative.Model
