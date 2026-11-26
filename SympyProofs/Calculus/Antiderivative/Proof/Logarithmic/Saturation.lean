module

public import SympyProofs.Calculus.Antiderivative.Spec.Logarithmic
public import SympyProofs.Calculus.Antiderivative.Proof.StepModel
public import SympyProofs.Calculus.Antiderivative.Extension.LogDeriv

/-! Closure of saturated logarithmic derivatives under rational linear combinations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

variable {F : Type*} [Field F]

/-- A logarithmic derivative after multiplication by a positive integer. -/
def Saturated (D : Model.Der F) (w : F) : Prop :=
  ∃ (m : ℕ) (v : F), 0 < m ∧ v ≠ 0 ∧ D v / v = m * w

/-- The logarithmic derivative of a nonzero field element has denominator one as a relation. -/
theorem saturated_log (D : Model.Der F) {v : F} (hv : v ≠ 0) :
    Saturated D (D v / v) := ⟨1, v, Nat.one_pos, hv, by simp⟩

/-- Zero is represented by the logarithmic derivative of one. -/
theorem saturated_zero (D : Model.Der F) : Saturated D 0 :=
  ⟨1, 1, Nat.one_pos, one_ne_zero, by simp⟩

/-- A common positive multiple gives the sum as the logarithmic derivative of a product. -/
theorem Saturated.add {D : Model.Der F} {u v : F} (hu : Saturated D u)
    (hv : Saturated D v) : Saturated D (u + v) := by
  obtain ⟨m, a, hm, ha, hea⟩ := hu
  obtain ⟨n, b, hn, hb, heb⟩ := hv
  refine ⟨m*n, a^n*b^m, Nat.mul_pos hm hn, mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb), ?_⟩
  rw [Extension.logDeriv_mul (pow_ne_zero _ ha) (pow_ne_zero _ hb), Extension.logDeriv_pow ha,
    Extension.logDeriv_pow hb, hea, heb, Nat.cast_mul]
  ring

/-- Inverting the representative negates the saturated logarithmic derivative. -/
theorem Saturated.neg {D : Model.Der F} {u : F} (hu : Saturated D u) :
    Saturated D (-u) := by
  obtain ⟨m, a, hm, ha, he⟩ := hu
  exact ⟨m, a⁻¹, hm, inv_ne_zero ha, by rw [Extension.logDeriv_inv ha, he]; ring⟩

/-- Multiplying a saturated logarithmic derivative by an arbitrary rational preserves it. -/
theorem Saturated.rat_mul [CharZero F] {D : Model.Der F} {u : F} (hu : Saturated D u) (r : ℚ) :
    Saturated D ((r : F) * u) := by
  obtain ⟨m, a, hm, ha, he⟩ := hu
  have zn (z : ℤ) : D (a^z) / a^z = (z : F) * (D a / a) := by
    cases z with
    | ofNat z => simpa using Extension.logDeriv_pow (D := D) ha z
    | negSucc z =>
      rw [zpow_negSucc, Extension.logDeriv_inv (pow_ne_zero _ ha), Extension.logDeriv_pow ha]
      push_cast
      ring
  refine ⟨m*r.den, a^r.num, Nat.mul_pos hm r.den_pos, zpow_ne_zero _ ha, ?_⟩
  rw [zn, he, Nat.cast_mul, Rat.cast_def]
  field_simp

/-- Rational multiples and finite sums of actual logarithmic derivatives are saturated. -/
theorem saturated_sum {D : Model.Der F} {ι : Type*} (s : Finset ι) (v : ι → F)
    (h : ∀ i ∈ s, Saturated D (v i)) : Saturated D (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using saturated_zero D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Saturation is invariant under a differential ring equivalence. -/
theorem saturated_equiv {G : Type*} [Field G] (D : Model.Der F)
    (E : Model.Der G) (e : F ≃+* G) (he : ∀ a, e (D a) = E (e a)) (w : F) :
    Saturated D w ↔ Saturated E (e w) := by
  constructor
  · rintro ⟨m, a, hm, ha, h⟩
    refine ⟨m, e a, hm, (map_ne_zero_iff e e.injective).mpr ha, ?_⟩
    rw [← he, ← map_div₀, h, map_mul, map_natCast]
  · rintro ⟨m, a, hm, ha, h⟩
    refine ⟨m, e.symm a, hm, (map_ne_zero_iff _ e.symm.injective).mpr ha, e.injective ?_⟩
    rw [map_div₀, he, e.apply_symm_apply, h, map_mul, map_natCast]

end SympyProofs.Calculus.Antiderivative.Logarithmic
