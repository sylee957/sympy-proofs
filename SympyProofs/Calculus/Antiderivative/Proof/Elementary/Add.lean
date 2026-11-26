module

public import SympyProofs.Calculus.Antiderivative.Program.Elementary
public import SympyProofs.Calculus.Antiderivative.Proof.Answer

/-! Elementary primitives and Liouville forms admit constant-linear combinations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable {t : Tower R n} {x y : M k n}

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

theorem Tower.Elementary.add (hx : t.Elementary k x) (hy : t.Elementary k y) :
    t.Elementary k (x + y) := by
  obtain ⟨a,logs,rfl⟩ := hx
  obtain ⟨b,more,rfl⟩ := hy
  exact ⟨a+b, logs++more, by simp [add_assoc, add_left_comm]⟩

theorem Tower.Elementary.mul_const (c : k) (hx : t.Elementary k x) :
    t.Elementary k (Model.C k n c * x) := by
  obtain ⟨a,logs,rfl⟩ := hx
  refine ⟨Model.C k n c * a, logs.map (fun (d,u) => (c*d,u)), ?_⟩
  have hc : t.modelD k (Model.C k n c) = 0 := Model.derivation_C k _ _
  rw [Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul, mul_add]
  congr 1
  induction logs with
  | nil => simp
  | cons z zs ih => rcases z with ⟨d,u⟩; simp [mul_add, ih, mul_assoc]

theorem Tower.Elementary.sub (hx : t.Elementary k x) (hy : t.Elementary k y) :
    t.Elementary k (x-y) := by
  simpa [sub_eq_add_neg] using hx.add k (hy.mul_const k (-1))

@[simp] theorem Answer.regular_add (a b : Answer R n) :
    (a.add b).Regular k ↔ a.Regular k ∧ b.Regular k := by
  simp only [add, Regular, List.mem_append]
  grind

@[simp] theorem Answer.deriv_add (t : Tower R n) (a b : Answer R n) :
    (a.add b).deriv k t = a.deriv k t + b.deriv k t := by
  simp [add, deriv, add_assoc, add_left_comm]

end SympyProofs.Calculus.Antiderivative
