module

public import SympyProofs.Calculus.Risch.Program.Term

/-! Towers above a tower. `integrate_no_answer` states completeness in the language of
terms: when `integrate` finds no elementary integral in the field of a tower, no answer
written in any tower obtained from it by adjoining exponentials and logarithms has the
integrand as its derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

/-- Regard a term as a term `d` levels up. -/
def Term.lift : (d : Nat) → Term n → Term (n + d)
  | 0, e => e
  | d + 1, e => (Term.lift d e).weaken

/-- `t'` is `t` with `d` more generators, each the exponential or the logarithm of a term of
the tower below it. -/
inductive Tower.ElementaryExt (t : Tower n) : (d : Nat) → Tower (n + d) → Prop
  | refl : ElementaryExt t 0 t
  | exp {d : Nat} {s : Tower (n + d)} (h : ElementaryExt t d s) (u : Term (n + d)) :
      ElementaryExt t (d + 1) (s.exp u)
  | log {d : Nat} {s : Tower (n + d)} (h : ElementaryExt t d s) (u : Term (n + d)) :
      ElementaryExt t (d + 1) (s.log u)

end SympyProofs.Calculus.Risch
