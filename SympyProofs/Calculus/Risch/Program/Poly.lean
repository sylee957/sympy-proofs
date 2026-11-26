module

public import SympyProofs.Calculus.Risch.Program.Normal
public import SympyProofs.Calculus.Risch.Program.ZPoly

/-! Polynomials in the newest generator. An element of the field of depth `n + 1` is a
quotient of two polynomials in the generator `n` whose coefficients are terms of depth `n`.
A polynomial is the list of its coefficients, lowest degree first. Division, greatest common
divisors and reduction to lowest terms use the zero test on the coefficients, and
`Term.norm` puts every coefficient in lowest terms, as a quotient of two polynomials with
integer coefficients in all the generators at once. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- A polynomial in the generator `n`, as the list of its coefficients from degree zero. -/
abbrev Poly (n : Nat) := List (Term n)

/-! Arithmetic on terms that evaluates rational constants as it goes. -/

namespace Coeff

variable {n : Nat}

/-- `a + b` and `a b` with integer arithmetic when both are integers: Lean's rational
arithmetic finds a greatest common divisor even then. -/
def ratAdd (a b : Rat) : Rat :=
  if a.den == 1 && b.den == 1 then ((a.num + b.num : Int) : Rat) else a + b

def ratMul (a b : Rat) : Rat :=
  if a.den == 1 && b.den == 1 then ((a.num * b.num : Int) : Rat) else a * b

def neg : Term n → Term n
  | .const a => .const (-a)
  | .neg a => a
  | a => .neg a

def add : Term n → Term n → Term n
  | .const a, .const b => .const (ratAdd a b)
  | .const a, b => if a == 0 then b else .add (.const a) b
  | a, .const b => if b == 0 then a else .add a (.const b)
  | a, b => .add a b

def mul : Term n → Term n → Term n
  | .const a, .const b => .const (ratMul a b)
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

/-- Divide every coefficient by the highest written one. -/
def monicWith (ν : Term n → Term n) (p : Poly n) : Poly n := p.map fun e => ν (.div e (lead p))

/-! The two Euclidean algorithms divide each remainder by its highest coefficient. Without
that, the coefficients of the remainders grow from step to step. The arguments themselves
are left as they are: dividing them would put their highest coefficients into the
denominators of all the others, which costs more than it saves. -/

/-- The extended Euclidean algorithm: a common divisor `g` of `a` and `b` and cofactors
with `u a + v b = g`, returned as `(g, u, v)`. -/
def xgcdWith (ν : Term n → Term n) : Nat → Poly n → Poly n → Poly n × Poly n × Poly n
  | 0, a, _ => (a, [.const 1], [])
  | fuel + 1, a, b =>
    if (trim b).isEmpty then (a, [.const 1], [])
    else
      let qr := divModWith ν (trim b) a.length a
      let r := trim qr.2
      if r.isEmpty then (trim b, [], [.const 1])
      else
        let s := xgcdWith ν fuel (trim b) (monicWith ν r)
        let u := s.2.2.map fun e => ν (.div e (lead r))
        (s.1, u, (sub s.2.1 (mul u qr.1)).map ν)

/-- A greatest common divisor with its cofactors. -/
def gcdWith (ν : Term n → Term n) (a b : Poly n) : Poly n × Poly n × Poly n :=
  xgcdWith ν (b.length + 1) a b

/-- The Euclidean algorithm, for a greatest common divisor without cofactors. -/
def euclidWith (ν : Term n → Term n) : Nat → Poly n → Poly n → Poly n
  | 0, a, _ => a
  | fuel + 1, a, b =>
    if (trim b).isEmpty then a
    else
      let r := trim (remWith ν a (trim b))
      if r.isEmpty then trim b else euclidWith ν fuel (trim b) (monicWith ν r)

/-- Divide a numerator and a denominator by their greatest common divisor. -/
def reduceWith (ν : Term n → Term n) (a b : Poly n) : Poly n × Poly n :=
  let g := trim (euclidWith ν (b.length + 1) a b)
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

/-- Lowest terms: a quotient of two polynomials with integer coefficients in all the
generators, reduced by their greatest common divisor. -/
def norm {n : Nat} (e : Term n) : Term n := ZP.normFF e

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
