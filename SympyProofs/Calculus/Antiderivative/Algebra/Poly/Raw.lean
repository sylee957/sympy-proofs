module

/-! Polynomials in one variable as plain lists: a polynomial is the list of its coefficients
from degree zero. Nothing is asked of the list, so the same polynomial has many lists: any
number of vanishing coefficients of highest degree may follow.

This file has the operations on such lists and nothing else: no theorem and no proposition.
Every operation that returns a list returns it trimmed, without vanishing coefficients of
highest degree (the helpers named `…Aux` do not). That is for speed, and nothing relies on
it.

The type the algorithms compute in is the quotient `Poly R` of `Poly/Basic.lean`, where two
lists with the same coefficients are equal, and where the operations of this file are those of
a commutative ring. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

universe u

/-- The coefficients from degree zero. Vanishing coefficients of highest degree may be
present. -/
abbrev Poly.Raw (R : Type) := List R

namespace Poly.Raw

variable {R : Type}

/-! ### What is read off a list -/

/-- Remove the vanishing coefficients of highest degree. A coefficient is compared with zero
only when all the coefficients after it vanish. -/
def trim [Zero R] [DecidableEq R] : Raw R → Raw R
  | [] => []
  | c :: cs =>
    let t := trim cs
    if t.isEmpty then (if c == 0 then [] else [c]) else c :: t

/-- The coefficient of degree `n`, zero beyond the end of the list. -/
def coeff [Zero R] (p : Raw R) (n : Nat) : R := List.getD p n 0

/-- The degree, and zero for the zero polynomial: one less than the length of the trimmed
list. -/
def natDegree [Zero R] [DecidableEq R] (p : Raw R) : Nat := List.length (trim p) - 1

/-- The coefficient of highest degree, and zero for the zero polynomial: the last element of
the trimmed list. -/
def leadingCoeff [Zero R] [DecidableEq R] (p : Raw R) : R := List.getLastD (trim p) 0

/-- The value at `x`, by Horner's rule. -/
def eval [Zero R] [Add R] [Mul R] (x : R) : Raw R → R
  | [] => 0
  | c :: cs => c + x * eval x cs

/-! ### Constants, the variable, monomials -/

/-- The constant polynomial. -/
def C [Zero R] [DecidableEq R] (a : R) : Raw R := if a == 0 then [] else [a]

/-- The variable. -/
def X [Zero R] [One R] [DecidableEq R] : Raw R := trim [0, 1]

/-- The polynomial `a Xⁿ`. -/
def monomial [Zero R] [DecidableEq R] (n : Nat) (a : R) : Raw R :=
  if a == 0 then [] else List.replicate n 0 ++ [a]

/-! ### Arithmetic -/

/-- The sum, coefficient by coefficient, not trimmed. -/
def addAux [Add R] : Raw R → Raw R → Raw R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addAux p q

/-- The sum. -/
def add [Zero R] [Add R] [DecidableEq R] (p q : Raw R) : Raw R := trim (addAux p q)

/-- The opposite. -/
def neg [Zero R] [Neg R] [DecidableEq R] (p : Raw R) : Raw R := trim (List.map (- ·) p)

/-- The difference, coefficient by coefficient, not trimmed. -/
def subAux [Neg R] [Sub R] : Raw R → Raw R → Raw R
  | [], q => List.map (- ·) q
  | p, [] => p
  | a :: p, b :: q => (a - b) :: subAux p q

/-- The difference. -/
def sub [Zero R] [Neg R] [Sub R] [DecidableEq R] (p q : Raw R) : Raw R := trim (subAux p q)

/-- The action of a scalar on every coefficient. For a scalar that is a coefficient it is the
product with that coefficient. -/
def smul {A : Type u} [SMul A R] [Zero R] [DecidableEq R] (a : A) (p : Raw R) : Raw R :=
  trim (List.map (a • ·) p)

/-- The product of `p` with `b :: q`, row by row, not trimmed. A row whose coefficient
vanishes costs nothing. -/
def mulAux [Zero R] [Add R] [Mul R] [DecidableEq R] (b : R) (q : Raw R) : Raw R → Raw R
  | [] => []
  | a :: p =>
    if a == 0 then 0 :: mulAux b q p
    else a * b :: addAux (List.map (a * ·) q) (mulAux b q p)

/-- The product. -/
def mul [Zero R] [Add R] [Mul R] [DecidableEq R] (p : Raw R) : Raw R → Raw R
  | [] => []
  | b :: q => trim (mulAux b q p)

/-- The power, by repeated product. -/
def pow [Zero R] [One R] [Add R] [Mul R] [DecidableEq R] (p : Raw R) : Nat → Raw R
  | 0 => C 1
  | n + 1 => mul (pow p n) p

/-! ### Derivative and change of coefficients -/

/-- The coefficients `k c₀, (k + 1) c₁, …` of a list `c₀, c₁, …`, not trimmed. -/
def derivativeAux [One R] [Add R] [Mul R] (k : R) : Raw R → Raw R
  | [] => []
  | c :: cs => k * c :: derivativeAux (k + 1) cs

/-- The formal derivative. -/
def derivative [Zero R] [One R] [Add R] [Mul R] [DecidableEq R] : Raw R → Raw R
  | [] => []
  | _ :: cs => trim (derivativeAux 1 cs)

/-- Apply a function to every coefficient of the trimmed list. The list is trimmed before, so
that the result depends only on the polynomial, whatever the function does to zero. -/
def map {S : Type} [Zero R] [DecidableEq R] [Zero S] [DecidableEq S] (f : R → S)
    (p : Raw R) : Raw S :=
  trim (List.map f (trim p))

/-! ### Division -/

/-- `p - c d` on the coefficients that `d` has, both lists from the highest degree down:
`c y` is subtracted from each element `x` of `p` that has an element `y` of `d` at the same
place, and the other elements of `p` are kept. -/
def subMulAux [Sub R] [Mul R] (c : R) : Raw R → Raw R → Raw R
  | [], _ => []
  | p, [] => p
  | x :: p, y :: d => (x - c * y) :: subMulAux c p d

/-- Long division, with the coefficients from the highest degree down. The divisor is
`b :: d`, with leading coefficient `b`; `p` is what is left of the dividend, `q` the
coefficients of the quotient found so far, from the lowest of them, and `k` the number of
coefficients of the quotient still to be found. A step divides the first coefficient of `p`
by `b` and subtracts that multiple of the divisor. The result is the quotient, from degree
zero, and the remainder, from the highest degree down. -/
def divModAux [Zero R] [Sub R] [Mul R] [Div R] [DecidableEq R] (b : R) (d : Raw R) :
    Nat → Raw R → Raw R → Raw R × Raw R
  | 0, p, q => (q, p)
  | _ + 1, [], q => (q, [])
  | k + 1, a :: p, q =>
    let c := a / b
    divModAux b d k (if c == 0 then p else subMulAux c p d) (c :: q)

/-- The quotient and the remainder of the long division of `p` by `d`: each step divides by
the leading coefficient of `d`, with the division of the coefficients. Both lists are trimmed
first, so that the result depends only on the two polynomials. Division by zero gives the
quotient zero and the remainder `p`. -/
def divMod [Zero R] [Sub R] [Mul R] [Div R] [DecidableEq R] (p d : Raw R) : Raw R × Raw R :=
  let p := trim p
  match List.reverse (trim d) with
  | [] => ([], p)
  | b :: d =>
    let r := divModAux b d (List.length p - List.length d) (List.reverse p) []
    (trim r.1, trim (List.reverse r.2))

end Poly.Raw

end SympyProofs.Calculus.Antiderivative
