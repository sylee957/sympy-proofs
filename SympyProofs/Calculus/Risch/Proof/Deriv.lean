module

public import SympyProofs.Calculus.Risch.Program.Deriv
public import SympyProofs.Calculus.Risch.Spec.Admissible
public import SympyProofs.Calculus.Risch.Proof.Derivative
public import SympyProofs.Calculus.Risch.Proof.Poly
import Mathlib.Tactic.Ring

/-! The derivation of the field of a tower step restricts to a derivation of the polynomial
ring in the newest generator, and the derivative of a coefficient list denotes the
derivative of the polynomial it denotes. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

noncomputable local instance intAlgebraDeriv {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Term

theorem defined_deriv {F : Type*} [Field F] {g : Fin n → F} {vel : Fin n → Term n}
    (hv : ∀ i, (vel i).Defined g) (e : Term n) (he : e.Defined g) : (e.deriv vel).Defined g := by
  induction e with
  | const => trivial
  | gen i => exact hv i
  | neg a ha => exact ha he
  | add a b ha hb | sub a b ha hb => exact ⟨ha he.1, hb he.2⟩
  | mul a b ha hb => exact ⟨⟨ha he.1, he.2⟩, he.1, hb he.2⟩
  | div a b ha hb =>
    exact ⟨⟨⟨ha he.1, he.2.1⟩, he.1, hb he.2.1⟩, ⟨he.2.1, he.2.1⟩, mul_ne_zero he.2.2 he.2.2⟩

end Term

namespace Tower

/-- The derivative of every generator of an admissible tower is defined. -/
theorem inDomain_vel {t : Tower n} (ht : t.Admissible k) (i : Fin n) :
    Term.InDomain k (t.vel i) := by
  induction t with
  | const => exact i.elim0
  | prim t b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [vel, Fin.lastCases_last]
      exact (Term.inDomain_weaken b).mpr ht.2.1
    · simp only [vel, Fin.lastCases_castSucc]
      exact (Term.inDomain_weaken _).mpr (ih ht.1 j)
  | exp t u ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [vel, Fin.lastCases_last]
      exact ⟨trivial, (Term.inDomain_weaken _).mpr
        (Term.defined_deriv (fun j => ih ht.1 j) u ht.2.1)⟩
    · simp only [vel, Fin.lastCases_castSucc]
      exact (Term.inDomain_weaken _).mpr (ih ht.1 j)

/-- The derivative of a defined term of an admissible tower is defined. -/
theorem inDomain_D {t : Tower n} (ht : t.Admissible k) {e : Term n} (he : Term.InDomain k e) :
    Term.InDomain k (t.D e) :=
  Term.defined_deriv (fun i => inDomain_vel ht i) e he

theorem parent_admissible {t : Tower (n + 1)} (ht : t.Admissible k) : t.parent.Admissible k := by
  cases t <;> exact ht.1

theorem inDomain_twist {t : Tower (n + 1)} (ht : t.Admissible k) : Term.InDomain k t.twist := by
  cases t with
  | prim t b => trivial
  | exp t u => exact inDomain_D ht.1 ht.2.1

theorem inDomain_shift {t : Tower (n + 1)} (ht : t.Admissible k) : Term.InDomain k t.shift := by
  cases t with
  | prim t b => exact ht.2.1
  | exp t u => trivial

variable (k)

/-- The derivation of the polynomial ring in the newest generator. -/
noncomputable def polyDer : Tower (n + 1) → Derivation ℤ (K k n)[X] (K k n)[X]
  | .prim t b =>
    letI : Differential (K k n) := ⟨t.der k⟩
    affine 0 (Term.value k b)
  | .exp t u =>
    letI : Differential (K k n) := ⟨t.der k⟩
    affine (t.der k (Term.value k u)) 0

variable {k}

/-- The derivation of the field restricts to the polynomial ring. -/
theorem der_algebraMap (t : Tower (n + 1)) (P : (K k n)[X]) :
    t.der k (algebraMap (K k n)[X] (RatFunc (K k n)) P) =
      algebraMap (K k n)[X] (RatFunc (K k n)) (polyDer k t P) := by
  cases t with
  | prim t b => exact extend_poly _ P
  | exp t u => exact extend_poly _ P

theorem value_twist (t : Tower (n + 1)) :
    Term.value k t.twist =
      match t with
      | .prim _ _ => 0
      | .exp t u => t.der k (Term.value k u) := by
  cases t with
  | prim t b => simp [twist, Term.value_const]
  | exp t u => exact (der_value t u).symm

theorem value_shift (t : Tower (n + 1)) :
    Term.value k t.shift =
      match t with
      | .prim _ b => Term.value k b
      | .exp _ _ => 0 := by
  cases t with
  | prim t b => rfl
  | exp t u => simp [shift, Term.value_const]

/-- The coefficients of the derivative of a polynomial in the newest generator. -/
theorem coeff_polyDer (t : Tower (n + 1)) (P : (K k n)[X]) (i : ℕ) :
    (polyDer k t P).coeff i = t.parent.der k (P.coeff i) +
      (i : K k n) * Term.value k t.twist * P.coeff i +
        ((i + 1 : ℕ) : K k n) * Term.value k t.shift * P.coeff (i + 1) := by
  cases t with
  | prim t b =>
    let _ : Differential (K k n) := ⟨t.der k⟩
    rw [value_twist, value_shift]
    change (affine 0 (Term.value k b) P).coeff i = _
    rw [coeff_affine]
    rfl
  | exp t u =>
    let _ : Differential (K k n) := ⟨t.der k⟩
    rw [value_twist, value_shift]
    change (affine (t.der k (Term.value k u)) 0 P).coeff i = _
    rw [coeff_affine]
    rfl

end Tower

namespace Poly

open Tower

/-- The derivative of a coefficient list denotes the derivative of the polynomial. -/
theorem model_der (t : Tower (n + 1)) (p : Poly n) :
    model k (der t p) = polyDer k t (model k p) := by
  ext i
  rw [der, coeff_model_map_range, coeff_polyDer]
  split
  · rw [Coeff.value_add, Coeff.value_add, Coeff.value_mul, Coeff.value_mul, Coeff.value_mul,
      Coeff.value_mul, ← der_value, value_coeff, value_coeff, Term.value_const, Term.value_const]
    push_cast
    ring
  · rename_i h
    rw [coeff_model_of_length_le (by omega : p.length ≤ i),
      coeff_model_of_length_le (by omega : p.length ≤ i + 1)]
    simp

theorem defined_der {t : Tower (n + 1)} (ht : t.Admissible k) {p : Poly n} (hp : Defined k p) :
    Defined k (der t p) := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  have ci := defined_coeff hp i
  exact Coeff.inDomain_add (inDomain_D (parent_admissible ht) ci)
    (Coeff.inDomain_add
      (Coeff.inDomain_mul (Coeff.inDomain_mul trivial (inDomain_twist ht)) ci)
      (Coeff.inDomain_mul (Coeff.inDomain_mul trivial (inDomain_shift ht))
        (defined_coeff hp (i + 1))))

end Poly

end SympyProofs.Calculus.Risch
