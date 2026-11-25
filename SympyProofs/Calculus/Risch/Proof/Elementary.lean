module

public import SympyProofs.Calculus.Risch.Spec.Elementary
public import SympyProofs.Calculus.Risch.Proof.Constants
import Mathlib.Tactic.Ring

/-! The elements with an elementary integral over the field of a tower form a vector space
over the constants that contains the derivatives and the logarithmic derivatives, and an
element with an elementary integral over a field has one over every field above it. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

noncomputable local instance intAlgebraElementary {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Tower.Elementary

variable {t : Tower n}

/-- A derivative has an elementary integral. -/
theorem der (v : K k n) : t.Elementary k (t.der k v) :=
  ⟨Empty, inferInstance, Empty.elim, Empty.elim, v, by simp⟩

theorem zero : t.Elementary k 0 := by
  have := der (k := k) (t := t) 0
  rwa [map_zero] at this

/-- A logarithmic derivative has an elementary integral. -/
theorem logDeriv (u : K k n) : t.Elementary k (t.der k u / u) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => u, 0, by simp⟩

theorem add {f g : K k n} (hf : t.Elementary k f) (hg : t.Elementary k g) :
    t.Elementary k (f + g) := by
  obtain ⟨ι, _, c, u, v, rfl⟩ := hf
  obtain ⟨κ, _, d, w, z, rfl⟩ := hg
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c d, Sum.elim u w, v + z, ?_⟩
  rw [Fintype.sum_sum_type, map_add]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- A constant multiple of an element with an elementary integral has one. -/
theorem const_mul (a : k) {f : K k n} (hf : t.Elementary k f) :
    t.Elementary k (constHom k n a * f) := by
  obtain ⟨ι, _, c, u, v, rfl⟩ := hf
  refine ⟨ι, inferInstance, fun i => a * c i, u, constHom k n a * v, ?_⟩
  rw [Derivation.leibniz, Tower.der_constHom, smul_zero, add_zero, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  ring

theorem neg {f : K k n} (hf : t.Elementary k f) : t.Elementary k (-f) := by
  have := const_mul (-1) hf
  simpa using this

theorem sub {f g : K k n} (hf : t.Elementary k f) (hg : t.Elementary k g) :
    t.Elementary k (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- An elementary integral over the field below a primitive is one over the field above. -/
theorem lift_prim {t : Tower n} (b : Term n) {f : K k n} (hf : t.Elementary k f) :
    (t.prim b).Elementary k (RatFunc.C f) := by
  obtain ⟨ι, _, c, u, v, rfl⟩ := hf
  refine ⟨ι, inferInstance, c, fun i => RatFunc.C (u i), RatFunc.C v, ?_⟩
  rw [map_add, map_sum, Tower.der_prim_C]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Tower.der_prim_C, map_mul, map_div₀]
  rfl

/-- An elementary integral over the field below an exponential is one over the field
above. -/
theorem lift_exp {t : Tower n} (u' : Term n) {f : K k n} (hf : t.Elementary k f) :
    (t.exp u').Elementary k (RatFunc.C f) := by
  obtain ⟨ι, _, c, u, v, rfl⟩ := hf
  refine ⟨ι, inferInstance, c, fun i => RatFunc.C (u i), RatFunc.C v, ?_⟩
  rw [map_add, map_sum, Tower.der_exp_C]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Tower.der_exp_C, map_mul, map_div₀]
  rfl

end Tower.Elementary

end SympyProofs.Calculus.Risch
