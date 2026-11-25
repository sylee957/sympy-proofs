module

/-! Terms and towers. A term of depth `n` is a rational expression in `n` numbered
generators. A tower of depth `n` says how each of them is adjoined: the generator on top of
a tower `t` of depth `n` has number `n` and is adjoined by a term of depth `n`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- A rational expression in `n` generators, with rational coefficients. -/
inductive Term (n : Nat)
  | const (q : Rat)
  | gen (i : Fin n)
  | neg (a : Term n)
  | add (a b : Term n)
  | sub (a b : Term n)
  | mul (a b : Term n)
  | div (a b : Term n)
  deriving Repr, DecidableEq, Inhabited

/-- A tower of generators over the constant field. A generator `θ` is adjoined as a
primitive, `θ′ = b`, or as an exponential, `θ′ = u′ θ`. -/
inductive Tower : Nat → Type
  | const : Tower 0
  | prim {n : Nat} (t : Tower n) (b : Term n) : Tower (n + 1)
  | exp {n : Nat} (t : Tower n) (u : Term n) : Tower (n + 1)
  deriving Repr

namespace Term

variable {n : Nat}

/-- Regard a term as a term of the next depth. -/
def weaken : Term n → Term (n + 1)
  | .const q => .const q
  | .gen i => .gen i.castSucc
  | .neg a => .neg a.weaken
  | .add a b => .add a.weaken b.weaken
  | .sub a b => .sub a.weaken b.weaken
  | .mul a b => .mul a.weaken b.weaken
  | .div a b => .div a.weaken b.weaken

/-- The derivative of a term, given the derivatives of the generators. -/
def deriv (vel : Fin n → Term n) : Term n → Term n
  | .const _ => .const 0
  | .gen i => vel i
  | .neg a => .neg (a.deriv vel)
  | .add a b => .add (a.deriv vel) (b.deriv vel)
  | .sub a b => .sub (a.deriv vel) (b.deriv vel)
  | .mul a b => .add (.mul (a.deriv vel) b) (.mul a (b.deriv vel))
  | .div a b => .div (.sub (.mul (a.deriv vel) b) (.mul a (b.deriv vel))) (.mul b b)

end Term

namespace Tower

/-- The derivative of each generator, as a term of the tower. -/
def vel : {n : Nat} → Tower n → Fin n → Term n
  | _, .const => fun i => i.elim0
  | _, .prim t b => Fin.lastCases b.weaken fun i => (vel t i).weaken
  | _, .exp (n := n) t u =>
    Fin.lastCases (.mul (.gen (Fin.last n)) (u.deriv (vel t)).weaken) fun i => (vel t i).weaken

/-- The derivative of a term of the tower. -/
def D {n : Nat} (t : Tower n) (e : Term n) : Term n := e.deriv t.vel

/-- The variable over the constants: the primitive of `1`. -/
def x : Tower 1 := .prim .const (.const 1)

/-- Adjoin the logarithm of `u`: the primitive of `u′/u`. -/
def log {n : Nat} (t : Tower n) (u : Term n) : Tower (n + 1) := .prim t (.div (t.D u) u)

end Tower

end SympyProofs.Calculus.Risch
