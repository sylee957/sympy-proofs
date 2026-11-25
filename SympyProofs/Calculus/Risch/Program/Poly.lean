module

public import SympyProofs.Calculus.Risch.Program.Normal

/-! Polynomials in the newest generator. An element of the field of depth `n + 1` is a
quotient of two polynomials in the generator `n` whose coefficients are terms of depth `n`.
A polynomial is the list of its coefficients, lowest degree first. Division, greatest common
divisors and reduction to lowest terms use the zero test on the coefficients, and
`Term.norm` puts a term in lowest terms at every depth. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- A polynomial in the generator `n`, as the list of its coefficients from degree zero. -/
abbrev Poly (n : Nat) := List (Term n)

/-! Arithmetic on terms that evaluates rational constants as it goes. -/

namespace Coeff

variable {n : Nat}

def neg : Term n → Term n
  | .const a => .const (-a)
  | .neg a => a
  | a => .neg a

def add : Term n → Term n → Term n
  | .const a, .const b => .const (a + b)
  | .const a, b => if a == 0 then b else .add (.const a) b
  | a, .const b => if b == 0 then a else .add a (.const b)
  | a, b => .add a b

def mul : Term n → Term n → Term n
  | .const a, .const b => .const (a * b)
  | .const a, b => if a == 0 then .const 0 else if a == 1 then b else .mul (.const a) b
  | a, .const b => if b == 0 then .const 0 else if b == 1 then a else .mul a (.const b)
  | a, b => .mul a b

def div : Term n → Term n → Term n
  | a, .const b => if b == 1 then a else .div a (.const b)
  | a, b => .div a b

end Coeff

namespace Poly

variable {n : Nat}

/-- The coefficient of degree `i`. -/
def coeff (p : Poly n) (i : Nat) : Term n := p.getD i (.const 0)

/-- The coefficient of highest written degree. -/
def lead (p : Poly n) : Term n := p.getLastD (.const 0)

def neg (p : Poly n) : Poly n := p.map Coeff.neg

/-- Multiply every coefficient by a term. -/
def scale (c : Term n) (p : Poly n) : Poly n := p.map (Coeff.mul c)

def add : Poly n → Poly n → Poly n
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => Coeff.add a b :: add p q

def sub (p q : Poly n) : Poly n := add p (neg q)

def mul : Poly n → Poly n → Poly n
  | [], _ => []
  | a :: p, q => add (scale a q) (.const 0 :: mul p q)

/-- The monomial `h θᵏ`. -/
def mono (k : Nat) (h : Term n) : Poly n := List.replicate k (.const 0) ++ [h]

/-- The derivative with respect to the generator. -/
def formalD (p : Poly n) : Poly n :=
  (List.range (p.length - 1)).map fun i =>
    Coeff.mul (.const ((i + 1 : Nat) : Rat)) (coeff p (i + 1))

/-- The polynomial as a term one level up. -/
def toTerm : Poly n → Term (n + 1)
  | [] => .const 0
  | a :: as => Coeff.add a.weaken (Coeff.mul (.gen (Fin.last n)) (toTerm as))

/-- Remove vanishing coefficients of highest degree. -/
def trim : Poly n → Poly n
  | [] => []
  | c :: cs => if (trim cs).isEmpty then (if c.isZero then [] else [c]) else c :: trim cs

/-- `p - c θᵏ d`. -/
def subShift (p : Poly n) (c : Term n) (k : Nat) (d : Poly n) : Poly n :=
  sub p (List.replicate k (.const 0) ++ scale c d)

/-- Long division by a polynomial whose highest written coefficient is not zero, simplifying
coefficients with `ν`. The result is the quotient and the remainder. -/
def divModWith (ν : Term n → Term n) (d : Poly n) : Nat → Poly n → Poly n × Poly n
  | 0, p => ([], p)
  | fuel + 1, p =>
    if Nat.blt p.length d.length then ([], p)
    else
      let c := ν (.div (lead p) (lead d))
      let k := p.length - d.length
      let r := divModWith ν d fuel ((subShift p c k d).map ν).dropLast
      (add r.1 (mono k c), r.2)

def quotWith (ν : Term n → Term n) (p d : Poly n) : Poly n := (divModWith ν d p.length p).1

def remWith (ν : Term n → Term n) (p d : Poly n) : Poly n := (divModWith ν d p.length p).2

/-- The extended Euclidean algorithm: a common divisor `g` of `a` and `b` and cofactors
with `u a + v b = g`, returned as `(g, u, v)`. -/
def xgcdWith (ν : Term n → Term n) : Nat → Poly n → Poly n → Poly n × Poly n × Poly n
  | 0, a, _ => (a, [.const 1], [])
  | fuel + 1, a, b =>
    if (trim b).isEmpty then (a, [.const 1], [])
    else
      let r := xgcdWith ν fuel (trim b) (remWith ν a (trim b))
      (r.1, r.2.2, (sub r.2.1 (mul r.2.2 (quotWith ν a (trim b)))).map ν)

/-- A greatest common divisor with its cofactors. -/
def gcdWith (ν : Term n → Term n) (a b : Poly n) : Poly n × Poly n × Poly n :=
  xgcdWith ν (b.length + 1) a b

/-- Divide a numerator and a denominator by their greatest common divisor. -/
def reduceWith (ν : Term n → Term n) (a b : Poly n) : Poly n × Poly n :=
  let g := trim (gcdWith ν a b).1
  (quotWith ν a g, quotWith ν b g)

/-- A numerator and a denominator for a term one level up, without cancellation. -/
def ofTerm : Term (n + 1) → Poly n × Poly n
  | .const a => ([.const a], [.const 1])
  | .gen i => (Fin.lastCases [.const 0, .const 1] (fun j => [.gen j]) i, [.const 1])
  | .neg a => (neg (ofTerm a).1, (ofTerm a).2)
  | .add a b =>
    (add (mul (ofTerm a).1 (ofTerm b).2) (mul (ofTerm b).1 (ofTerm a).2),
      mul (ofTerm a).2 (ofTerm b).2)
  | .sub a b =>
    (sub (mul (ofTerm a).1 (ofTerm b).2) (mul (ofTerm b).1 (ofTerm a).2),
      mul (ofTerm a).2 (ofTerm b).2)
  | .mul a b => (mul (ofTerm a).1 (ofTerm b).1, mul (ofTerm a).2 (ofTerm b).2)
  | .div a b => (mul (ofTerm a).1 (ofTerm b).2, mul (ofTerm a).2 (ofTerm b).1)

end Poly

namespace Term

/-- The rational number denoted by a term without generators. -/
def evalRat : Term 0 → Rat
  | .const q => q
  | .gen i => i.elim0
  | .neg a => -a.evalRat
  | .add a b => a.evalRat + b.evalRat
  | .sub a b => a.evalRat - b.evalRat
  | .mul a b => a.evalRat * b.evalRat
  | .div a b => a.evalRat / b.evalRat

/-- Lowest terms. A constant is evaluated. At depth `n + 1` the numerator and denominator
are polynomials in the newest generator without a common factor, the denominator has leading
coefficient one, and the coefficients are in lowest terms. -/
def norm : {n : Nat} → Term n → Term n
  | 0, e => .const e.evalRat
  | n + 1, e =>
    let rd := Poly.reduceWith (norm (n := n)) (Poly.ofTerm e).1 (Poly.ofTerm e).2
    let den := Poly.trim rd.2
    let c := Poly.lead den
    Coeff.div (Poly.toTerm (rd.1.map fun a => norm (.div a c)))
      (Poly.toTerm (den.map fun a => norm (.div a c)))

end Term

namespace Poly

variable {n : Nat}

/-- Put every coefficient in lowest terms. -/
def norm (p : Poly n) : Poly n := p.map Term.norm

def quot (p d : Poly n) : Poly n := quotWith Term.norm p d

def rem (p d : Poly n) : Poly n := remWith Term.norm p d

/-- A greatest common divisor `g` of `a` and `b` with cofactors, `u a + v b = g`, as
`(g, u, v)`. -/
def gcd (a b : Poly n) : Poly n × Poly n × Poly n := gcdWith Term.norm a b

/-- Lowest terms of the quotient `a / b`. -/
def reduce (a b : Poly n) : Poly n × Poly n := reduceWith Term.norm a b

end Poly

end SympyProofs.Calculus.Risch
