module

public import SympyProofs.Calculus.Risch.Program.Poly

/-! The result of integration. An elementary integral is an element of the field plus sums
of logarithms. Each sum runs over the roots `c` of a polynomial and has the form
`Σ c log (arg c)`, where the argument is an element of the field depending on the root. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Term

/-- Renumber the generators. -/
def rename {m : Nat} (f : Fin n → Fin m) : Term n → Term m
  | .const q => .const q
  | .gen i => .gen (f i)
  | .neg a => .neg (a.rename f)
  | .add a b => .add (a.rename f) (b.rename f)
  | .sub a b => .sub (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)
  | .div a b => .div (a.rename f) (b.rename f)

/-- The power `θᵏ` of the newest generator. -/
def genPow (n : Nat) : Nat → Term (n + 1)
  | 0 => .const 1
  | k + 1 => .mul (genPow n k) (.gen (Fin.last n))

end Term

/-- The sum `Σ c log (arg c)` over the roots `c` of `modulus`. The modulus is a polynomial
in the root with coefficients in the field, and `arg` is a term in which the last generator
stands for the root. -/
structure RootSum (n : Nat) where
  modulus : Poly n
  arg : Term (n + 1)
  deriving Repr

/-- An elementary function over the field of a tower: an element of the field plus sums of
logarithms. -/
structure Answer (n : Nat) where
  field : Term n
  sums : List (RootSum n)
  deriving Repr

/-- The outcome of integration. -/
inductive Result (n : Nat)
  | elementary (a : Answer n)
  | nonelementary
  deriving Repr

namespace RootSum

/-- The same sum one level up. The root remains the last generator. -/
def weaken (s : RootSum n) : RootSum (n + 1) :=
  ⟨s.modulus.map Term.weaken,
    s.arg.rename (Fin.lastCases (Fin.last (n + 1)) fun i => i.castSucc.castSucc)⟩

end RootSum

namespace Answer

def weaken (a : Answer n) : Answer (n + 1) := ⟨a.field.weaken, a.sums.map RootSum.weaken⟩

/-- Add an element of the field. -/
def addField (W : Term n) (a : Answer n) : Answer n := ⟨.add W a.field, a.sums⟩

end Answer

end SympyProofs.Calculus.Risch
