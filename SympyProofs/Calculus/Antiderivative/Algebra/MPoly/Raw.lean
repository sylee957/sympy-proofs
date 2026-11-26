module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Prod.Lex.Basic
public import SympyProofs.Calculus.Antiderivative.Algebra.Poly.Raw

/-! Sparse polynomials with the exponent of variable zero first. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- The exponents of a monomial, with missing entries understood as zero. -/
abbrev Mono := List ℕ

namespace Mono

/-- Remove trailing zero exponents. -/
abbrev trim (e : Mono) : Mono := Poly.Raw.trim e

/-- Add exponents coordinate by coordinate. -/
abbrev add (e d : Mono) : Mono := Poly.Raw.addAux e d

/-- Total degree followed by the exponent list, ordered lexicographically. -/
def key (e : Mono) : Lex (ℕ × List ℕ) := toLex (e.sum, e)

/-- Compare exponent vectors without allocating an ordered pair for each comparison. -/
def lexLess : Mono → Mono → Bool
  | [], b => !b.isEmpty
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then lexLess as bs else a < b

/-- Whether the first monomial comes before the second in descending graded lexicographic order. -/
@[inline] def before (e d : Mono) : Bool :=
  let de := e.sum
  let dd := d.sum
  if dd == de then lexLess d e else dd < de

/-- Subtract exponents when the second monomial divides the first. -/
def quotient? : Mono → Mono → Option Mono
  | e, [] => some e
  | [], _ :: _ => none
  | i :: e, j :: d =>
    if j ≤ i then (quotient? e d).map ((i - j) :: ·) else none

/-- The exponents of the given power of one variable. -/
def power (i k : ℕ) : Mono := if k = 0 then [] else List.replicate i 0 ++ [k]

end Mono

/-- A list of monomials with coefficients, allowing repeated terms and zero coefficients. -/
abbrev MPoly.Raw (R : Type*) := List (Mono × R)

namespace MPoly.Raw

variable {R : Type*}

/-- Insert a term into sorted terms, combining like terms and removing a zero coefficient. -/
def insert [AddZeroClass R] [DecidableEq R] (e : Mono) (c : R) : Raw R → Raw R
  | [] => if c = 0 then [] else [(e, c)]
  | (d, a) :: p =>
    if c = 0 then (d, a) :: p
    else if e = d then
      if c + a = 0 then p else (e, c + a) :: p
    else if e.before d then (e, c) :: (d, a) :: p
    else (d, a) :: insert e c p

/-- Sort terms, combine duplicates, and drop terms outside the first `n` variables. -/
def normalize [AddZeroClass R] [DecidableEq R] (n : ℕ) : Raw R → Raw R
  | [] => []
  | (e, c) :: p =>
    let d := e.trim
    if d.length ≤ n then insert d c (normalize n p) else normalize n p

/-- The polynomial with constant value `c`. -/
def C [Zero R] [DecidableEq R] (c : R) : Raw R :=
  if c = 0 then [] else [([], c)]

/-- Variable number `i`, or zero if it is outside the first `n` variables. -/
def X [Zero R] [One R] [DecidableEq R] (n i : ℕ) : Raw R :=
  if i < n && (1 : R) != 0 then [(Mono.power i 1, 1)] else []

/-- Merge two term streams, adding matching heads. Arithmetic usually supplies sorted
streams, so equal powers meet before the final normalization. -/
def merge [AddZeroClass R] [DecidableEq R] : Raw R → Raw R → Raw R
  | [], q => q
  | p, [] => p
  | (e,a) :: ps, (d,b) :: qs =>
    if e = d then
      let tail := merge ps qs
      if a + b = 0 then tail else (e,a+b) :: tail
    else if e.before d then (e,a) :: merge ps ((d,b) :: qs)
    else (d,b) :: merge ((e,a) :: ps) qs

/-- The sum of two sparse polynomials. -/
def add [AddZeroClass R] [DecidableEq R] (n : ℕ) (p q : Raw R) : Raw R :=
  normalize n (merge p q)

/-- Negate every coefficient. -/
def neg [AddGroup R] [DecidableEq R] (n : ℕ) (p : Raw R) : Raw R :=
  normalize n (p.map fun (e, c) => (e, -c))

/-- The difference of two sparse polynomials. -/
def sub [AddGroup R] [DecidableEq R] (n : ℕ) (p q : Raw R) : Raw R :=
  add n p (neg n q)

/-- Each term of the first factor supplies a row in the order of the second factor. -/
def productRows [NonUnitalNonAssocSemiring R] [DecidableEq R] (q : Raw R) : Raw R → Raw R
  | [] => []
  | (e,a) :: ps => merge (q.map fun (d,b) => (Mono.add e d, a*b)) (productRows q ps)

/-- Multiply terms by adding their exponents and multiplying their coefficients. -/
def mul [NonUnitalNonAssocSemiring R] [DecidableEq R] (n : ℕ) (p q : Raw R) : Raw R :=
  normalize n (productRows q p)

/-- The partial derivative with respect to variable number `i`. -/
def «partial» [Semiring R] [DecidableEq R] (n i : ℕ) (p : Raw R) : Raw R :=
  if i < n then
    normalize n (p.map fun (e, c) => (e.modify i (· - 1), (e.getD i 0 : R) * c))
  else []

variable [CommRing R] [DecidableEq R]

/-- Multiply a sparse polynomial by a single term. -/
def mulTerm (n : ℕ) (e : Mono) (c : R) (p : Raw R) : Raw R :=
  normalize n (p.map fun (d, a) => (Mono.add e d, c * a))

/-- Successive leading terms of an exact quotient, accumulated in reverse order. -/
def divTerms [Div R] (n : ℕ) (d : Raw R) (lead : Mono × R) :
    ℕ → Raw R → Raw R → Option (Raw R)
  | _, [], q => some q.reverse
  | 0, _ :: _, _ => none
  | fuel + 1, (e, a) :: p, q =>
    match Mono.quotient? e lead.1 with
    | none => none
    | some f =>
      let c := a / lead.2
      if c * lead.2 = a then
        let f := f.trim
        let r := sub n ((e, a) :: p) (mulTerm n f c d)
        divTerms n d lead fuel r ((f, c) :: q)
      else none

/-- Propose an exact quotient from normalized terms, dividing scalars coefficient by coefficient.
For graded long division the total degree bounds every exponent reached. -/
def divideNormalized [Div R] (n : ℕ) (a b : Raw R) (lead : Mono × R) : Option (Raw R) :=
  if lead.1.isEmpty then some (a.map fun (e, c) => (e, c / lead.2))
  else
    let degree := (a.head?.map (fun t => t.1.sum)).getD 0
    divTerms n b lead ((degree + 1) ^ n) a []

/-- Divide by a nonzero polynomial and check the result by multiplying back. -/
def divExact? [Div R] (n : ℕ) (p d : Raw R) : Option (Raw R) := do
  let a := normalize n p
  let b := normalize n d
  let lead ← b.head?
  let q ← divideNormalized n a b lead
  if mul n q d = a then some q else none

/-- The degree in variable `i`, or zero for the zero polynomial. -/
def degreeIn (i : ℕ) (p : Raw R) : ℕ :=
  p.foldl (fun m t => max m (t.1.getD i 0)) 0

/-- The coefficient of the given power of the last variable. -/
def coeffAt (i k : ℕ) (p : Raw R) : Raw R :=
  normalize i (p.filterMap fun (e, c) => if e.getD i 0 = k then some (e.take i, c) else none)

/-- Multiply by the unit that normalizes the leading coefficient. -/
def normalizeLead [NormalizedGCDMonoid R] (n : ℕ) (p : Raw R) : Raw R :=
  match p with
  | [] => []
  | (_, a) :: _ =>
    let u : R := normUnit a
    if u = 1 then p else mulTerm n [] u p

/-- The pseudo-remainder in the last variable, by successive cancellations of its top power. -/
def pseudoRem (i : ℕ) (d : Raw R) (k : ℕ) (lc : Raw R) : ℕ → Raw R → Raw R
  | 0, p => p
  | fuel + 1, p =>
    let j := degreeIn i p
    if p.isEmpty || j < k then p
    else
      let u := mulTerm (i + 1) (Mono.power i (j - k)) 1 (coeffAt i j p)
      let r := sub (i + 1) (mul (i + 1) lc p) (mul (i + 1) u d)
      pseudoRem i d k lc fuel r

/-- The content in the last variable and the polynomial divided by that content. -/
def contentPrimitive [Div R] (i : ℕ) (gcdBelow : Raw R → Raw R → Raw R)
    (p : Raw R) : Raw R × Raw R := Id.run do
  let one : Raw R := C 1
  let mut c : Raw R := []
  for k in (p.map (fun t => t.1.getD i 0)).eraseDups do
    c := gcdBelow c (coeffAt i k p)
    if c == one then return (one, p)
  match divExact? (i + 1) p c with
  | some pp => return (c, pp)
  | none => return (one, p)

/-- The last nonzero primitive pseudo-remainder in variable number `i`. -/
def primitiveGCD [Div R] (i : ℕ) (gcdBelow : Raw R → Raw R → Raw R) :
    ℕ → Raw R → Raw R → Raw R
  | 0, a, _ => a
  | fuel + 1, a, b =>
    if b.isEmpty then a
    else
      let k := degreeIn i b
      if k = 0 then C 1
      else
        let j := degreeIn i a
        let r := pseudoRem i b k (coeffAt i k b) (j + 1) a
        if r.isEmpty then b
        else primitiveGCD i gcdBelow fuel b (contentPrimitive i gcdBelow r).2

/-- The greatest common divisor of all scalar coefficients, stopping at a unit. -/
def scalarContent [NormalizedGCDMonoid R] (p : Raw R) : R := Id.run do
  let mut g : R := 0
  for (_, a) in p do
    g := gcd g a
    if g = 1 then break
  return g

/-- Common divisor when the first input has total degree at most one. Its primitive part
is either a unit or a linear polynomial and hence has no proper nonconstant factor. -/
def linearGCD [Div R] [NormalizedGCDMonoid R] (n : ℕ) (p q : Raw R) : Raw R :=
  let cp := scalarContent p
  let c := gcd cp (scalarContent q)
  if (p.head?.map fun t => t.1.isEmpty).getD true then C c
  else
    let pp := if cp = 1 then p else p.map fun (e, a) => (e, a / cp)
    if (divExact? n q pp).isSome then normalizeLead n (mulTerm n [] c pp) else C c

/-- Coefficients in descending powers of the first variable, including internal zeroes. -/
def descendingCoeffs (p : Raw R) (d : ℕ) : List R :=
  (p.foldl (fun a (e,c) => a.set! (d - e.getD 0 0) c) (Array.replicate (d+1) 0)).toList

/-- Scale and subtract two descending rows, aligning their leading terms. -/
def subScaled (a b : R) : List R → List R → List R
  | [], _ => []
  | p, [] => if a = 1 then p else p.map (a * ·)
  | x :: xs, y :: ys => (a*x-b*y) :: subScaled a b xs ys

/-- Extract scalar content between successive pseudo-remainders. -/
def primitiveCoeffs [Div R] [NormalizedGCDMonoid R] (p : List R) : List R := Id.run do
  let mut g := 0
  for x in p do
    g := gcd g x
    if g == 1 then return p
  return p.map (· / g)

/-- Cancel the leading coefficients with their least scalar multipliers. -/
def densePseudoRem [Div R] [NormalizedGCDMonoid R] (B : R) (bs : List R) :
    ℕ → List R → List R
  | 0, p => p
  | _ + 1, [] => []
  | fuel + 1, a :: as =>
    if as.length < bs.length then a :: as
    else
      let g := gcd B a
      let r := (subScaled (B / g) (a / g) as bs).dropWhile (· == 0)
      densePseudoRem B bs fuel r

/-- Primitive Euclidean remainders for a dense univariate input. -/
def denseGCDLoop [Div R] [NormalizedGCDMonoid R] : ℕ → List R → List R → List R
  | _, a, [] => a
  | 0, _, b => b
  | _ + 1, _, [_] => [1]
  | fuel + 1, a, b :: bs =>
    let r := densePseudoRem b bs a.length a
    denseGCDLoop fuel (b :: bs) (primitiveCoeffs r)

/-- Compute a candidate using dense univariate arithmetic while keeping sparse inputs
in the sparse algorithm. The caller checks both exact divisions. -/
def denseGCD [Div R] [NormalizedGCDMonoid R] (p q : Raw R) (d e : ℕ) : Raw R :=
  let a := primitiveCoeffs (descendingCoeffs p d)
  let b := primitiveCoeffs (descendingCoeffs q e)
  let h := if d < e then denseGCDLoop (d+2) b a else denseGCDLoop (e+2) a b
  let c := gcd (scalarContent p) (scalarContent q)
  normalizeLead 1 ((h.reverse.zipIdx.filterMap fun (x,i) =>
    if x = 0 then none else some (Mono.power 0 i, c*x)).reverse)

/-- The primitive Euclidean algorithm on normalized polynomials, recursively taking
contents in one fewer variable. -/
def gcdAux [Div R] [NormalizedGCDMonoid R] : ℕ → Raw R → Raw R → Raw R
  | 0, p, q =>
    let constant (a : Raw R) := (a.head?.map Prod.snd).getD 0
    C (gcd (constant p) (constant q))
  | i + 1, p, q =>
    if p.isEmpty then normalizeLead (i + 1) q
    else if q.isEmpty || p == q then normalizeLead (i + 1) p
    else if p == C 1 || q == C 1 then C 1
    else if (p.head?.map fun t => t.1.sum).getD 0 ≤ 1 then linearGCD (i + 1) p q
    else if (q.head?.map fun t => t.1.sum).getD 0 ≤ 1 then linearGCD (i + 1) q p
    else if i = 0 && ((p.head?.map fun t => t.1.sum).getD 0 +
        (q.head?.map fun t => t.1.sum).getD 0) ≤ 4 * (p.length + q.length) then
      denseGCD p q (degreeIn 0 p) (degreeIn 0 q)
    else
      let (cp, a) := contentPrimitive i (gcdAux i) p
      let (cq, b) := contentPrimitive i (gcdAux i) q
      let c := gcdAux i cp cq
      let j := degreeIn i a
      let k := degreeIn i b
      let h := if j < k then primitiveGCD i (gcdAux i) (j + 2) b a
        else primitiveGCD i (gcdAux i) (k + 2) a b
      normalizeLead (i + 1) (mul (i + 1) c h)

/-- Substitute the same indeterminate for every variable. -/
def diagonal (p : Raw R) : Raw R :=
  normalize 1 (p.map fun (e, c) => (Mono.power 0 e.sum, c))

/-- Total degree of sorted terms. -/
def totalDegree (p : Raw R) : ℕ := (p.head?.map fun t => t.1.sum).getD 0

/-- A candidate common divisor, computed by the primitive Euclidean algorithm.
A degree-preserving diagonal specialization with coprime images excludes a nonconstant
common factor. Checking that first avoids multivariate pseudo-division on coprime inputs. -/
def commonDivisor [Div R] [NormalizedGCDMonoid R] (n : ℕ) (p q : Raw R) : Raw R :=
  let a := normalize n p
  let b := normalize n q
  if 1 < n && 1 < totalDegree a && 1 < totalDegree b then
    let u := diagonal a
    let v := diagonal b
    if (totalDegree u = totalDegree a || totalDegree v = totalDegree b) &&
        totalDegree (gcdAux 1 u v) = 0 then
      C (gcd (scalarContent a) (scalarContent b))
    else gcdAux n a b
  else gcdAux n a b

end MPoly.Raw

end SympyProofs.Calculus.Antiderivative
