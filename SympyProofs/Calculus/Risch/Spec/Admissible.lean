module

public import SympyProofs.Calculus.Risch.Spec.Derivation

/-! Admissible towers: each generator is transcendental over the field below it and adds no
constant. A primitive of `b` is admissible when `b` is defined and has no primitive in the
field below. An exponential of `u` is admissible when `u` is defined and no positive
multiple of `u′` is a logarithmic derivative in the field below. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable (k : Type) [Field k] [CharZero k]

/-- The conditions for a tower of transcendental generators with no new constants. -/
def Tower.Admissible : {n : ℕ} → Tower n → Prop
  | _, .const => True
  | _, .prim (n := n) t b =>
    t.Admissible ∧ Term.InDomain k b ∧ ¬ ∃ v : K k n, t.der k v = Term.value k b
  | _, .exp (n := n) t u =>
    t.Admissible ∧ Term.InDomain k u ∧
      ¬ ∃ (m : ℕ) (v : K k n), 0 < m ∧ v ≠ 0 ∧
        t.der k v / v = (m : K k n) * t.der k (Term.value k u)

end SympyProofs.Calculus.Risch
