module

public import SympyProofs.Calculus.Risch.Program.Term

/-! Fraction-free lowest terms. A term of depth `n` is written as a quotient of two
polynomials with integer coefficients in all `n` generators at once, reduced by greatest
common divisors over the integers. This avoids rational arithmetic, which finds a greatest
common divisor after every operation, and fractions nested one level inside another.

The greatest common divisor is found by the heuristic method of Char, Geddes and Gonnet,
with a primitive Euclidean algorithm when the heuristic gives up. Nothing is proved about
it: a candidate is used only after exact division by it has succeeded, so lowest terms keep
the value of a term whatever it returns (`ZP.normFF_spec`). -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- Polynomials with integer coefficients in `n` variables. For `n + 1` variables, the list
of coefficients in the last one, lowest degree first, each a polynomial in the others,
without vanishing coefficients of highest degree. -/
def ZP : Nat → Type
  | 0 => Int
  | n + 1 => List (ZP n)

namespace ZP

@[inline] def toInt (a : ZP 0) : Int := a
@[inline] def ofInt (a : Int) : ZP 0 := a
@[inline] def toList {n : Nat} (p : ZP (n + 1)) : List (ZP n) := p
@[inline] def ofList {n : Nat} (p : List (ZP n)) : ZP (n + 1) := p

/-! ### Lists of coefficients -/

/-- Drop the vanishing coefficients of highest degree. -/
def trimL {α : Type} (z : α → Bool) : List α → List α
  | [] => []
  | a :: as =>
    match trimL z as with
    | [] => if z a then [] else [a]
    | t => a :: t

def addL {α : Type} (add : α → α → α) : List α → List α → List α
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: addL add p q

def beqL {α : Type} (e : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: p, b :: q => e a b && beqL e p q
  | _, _ => false

/-! ### Arithmetic -/

def zero : (n : Nat) → ZP n
  | 0 => ofInt 0
  | _ + 1 => ofList []

def isZero : (n : Nat) → ZP n → Bool
  | 0, a => toInt a == 0
  | _ + 1, p => (toList p).isEmpty

def beq : (n : Nat) → ZP n → ZP n → Bool
  | 0, a, b => toInt a == toInt b
  | n + 1, p, q => beqL (beq n) (toList p) (toList q)

def const : (n : Nat) → Int → ZP n
  | 0, a => ofInt a
  | n + 1, a => ofList (if a == 0 then [] else [const n a])

def one (n : Nat) : ZP n := const n 1

/-- The polynomial of the variable `i`. -/
def var : (n : Nat) → Fin n → ZP n
  | 0, i => i.elim0
  | n + 1, i =>
    if h : i.val = n then ofList [zero n, one n]
    else ofList [var n ⟨i.val, by have := i.isLt; omega⟩]

/-- Whether the polynomial has no variables. -/
def isConst : (n : Nat) → ZP n → Bool
  | 0, _ => true
  | n + 1, p =>
    match toList p with
    | [] => true
    | [c] => isConst n c
    | _ => false

def add : (n : Nat) → ZP n → ZP n → ZP n
  | 0, a, b => ofInt (toInt a + toInt b)
  | n + 1, p, q => ofList (trimL (isZero n) (addL (add n) (toList p) (toList q)))

def neg : (n : Nat) → ZP n → ZP n
  | 0, a => ofInt (-toInt a)
  | n + 1, p => ofList ((toList p).map (neg n))

def sub (n : Nat) (p q : ZP n) : ZP n := add n p (neg n q)

/-- Multiply by an integer. -/
def smul : (n : Nat) → Int → ZP n → ZP n
  | 0, c, a => ofInt (c * toInt a)
  | n + 1, c, p => if c == 0 then zero (n + 1) else ofList ((toList p).map (smul n c))

/-- The product of coefficient lists, given the product of coefficients. -/
def mulL {α : Type} (z : α) (add mul : α → α → α) : List α → List α → List α
  | [], _ => []
  | a :: p, q => addL add (q.map (mul a)) (z :: mulL z add mul p q)

def mul : (n : Nat) → ZP n → ZP n → ZP n
  | 0, a, b => ofInt (toInt a * toInt b)
  | n + 1, p, q =>
    if (toList p).isEmpty || (toList q).isEmpty then zero (n + 1)
    else ofList (trimL (isZero n) (mulL (zero n) (add n) (mul n) (toList p) (toList q)))

/-- The highest coefficient in the last variable. -/
def lead {n : Nat} (p : ZP (n + 1)) : ZP n := (toList p).getLastD (zero n)

/-- The integer coefficient that leads in every variable, from the last. -/
def leadInt : (n : Nat) → ZP n → Int
  | 0, a => toInt a
  | n + 1, p => leadInt n (lead p)

/-- The largest absolute value of a coefficient. -/
def maxAbs : (n : Nat) → ZP n → Nat
  | 0, a => (toInt a).natAbs
  | n + 1, p => (toList p).foldl (fun m c => max m (maxAbs n c)) 0

/-- The greatest common divisor of the integer coefficients. -/
def icont : (n : Nat) → ZP n → Nat
  | 0, a => (toInt a).natAbs
  | n + 1, p => (toList p).foldl (fun g c => Nat.gcd g (icont n c)) 0

/-- Divide every coefficient by an integer that divides it. -/
def divInt : (n : Nat) → ZP n → Int → ZP n
  | 0, a, c => ofInt (toInt a / c)
  | n + 1, p, c => ofList ((toList p).map fun e => divInt n e c)

/-- Evaluate the last variable at an integer. -/
def evalLast (n : Nat) (p : ZP (n + 1)) (x : Int) : ZP n :=
  (toList p).foldr (fun c acc => add n c (smul n x acc)) (zero n)

/-- The residue of every coefficient modulo `m` in `(-m/2, m/2]`. -/
def smodP : (n : Nat) → ZP n → Int → ZP n
  | 0, a, m =>
    let r := toInt a % m
    ofInt (if 2 * r > m then r - m else r)
  | n + 1, p, m => ofList (trimL (isZero n) ((toList p).map fun e => smodP n e m))

/-- Make the leading integer coefficient positive. -/
def fixSign (n : Nat) (p : ZP n) : ZP n := if leadInt n p < 0 then neg n p else p

/-- Divide by the integer content and make the leading integer coefficient positive. -/
def primZ (n : Nat) (p : ZP n) : ZP n :=
  let c := icont n p
  fixSign n (if c ≤ 1 then p else divInt n p c)

/-- `p - c xᵏ q` for coefficient lists. -/
def subShift (n : Nat) (p : List (ZP n)) (c : ZP n) (k : Nat) (q : List (ZP n)) :
    List (ZP n) :=
  trimL (isZero n) (addL (add n) p (List.replicate k (zero n) ++ q.map fun e => neg n (mul n c e)))

/-- Long division of coefficient lists that fails unless it is exact, given exact division
of the coefficients: the quotient. -/
def divLoop (n : Nat) (dex : ZP n → ZP n → Option (ZP n)) (dl : List (ZP n)) (ld : ZP n) :
    Nat → List (ZP n) → Option (List (ZP n))
  | 0, _ => none
  | fuel + 1, p =>
    if p.isEmpty then some []
    else if p.length < dl.length then none
    else
      let k := p.length - dl.length
      match dex (p.getLastD (zero n)) ld with
      | none => none
      | some c =>
        (divLoop n dex dl ld fuel (subShift n p c k dl)).map fun q =>
          trimL (isZero n) (addL (add n) q (List.replicate k (zero n) ++ [c]))

/-- Exact division: `some q` with `p = q d`, or `none`. -/
def divExact? : (n : Nat) → ZP n → ZP n → Option (ZP n)
  | 0, a, b =>
    if toInt b == 0 then none
    else if toInt a % toInt b == 0 then some (ofInt (toInt a / toInt b)) else none
  | n + 1, p, d =>
    let dl := toList d
    if dl.isEmpty then none
    else (divLoop n (divExact? n) dl (dl.getLastD (zero n)) ((toList p).length + 1)
      (toList p)).map ofList

/-- A remainder of `p` by `d` after multiplying `p` by a power of the leading coefficient of
`d`, for coefficient lists with `d` not empty. -/
def premL (n : Nat) (d : List (ZP n)) : Nat → List (ZP n) → List (ZP n)
  | 0, p => p
  | fuel + 1, p =>
    if p.length < d.length then p
    else
      let k := p.length - d.length
      let lp := p.getLastD (zero n)
      let ld := d.getLastD (zero n)
      premL n d fuel (subShift n (p.map (mul n ld)) lp k d)

/-! ### Greatest common divisors -/

/-- The digits of `h` in base `x`, taken in `(-x/2, x/2]`, as the coefficients of a
polynomial in a new last variable. -/
def interpolate (n : Nat) (h : ZP n) (x : Int) : ZP (n + 1) :=
  ofList (trimL (isZero n) (go (Nat.log2 (maxAbs n h) + 2) h))
where
  go : Nat → ZP n → List (ZP n)
    | 0, _ => []
    | fuel + 1, h =>
      if isZero n h then []
      else
        let g := smodP n h x
        g :: go fuel (divInt n (sub n h g) x)

/-- A square root within a factor of two, enough for choosing evaluation points. -/
def isqrt (a : Nat) : Nat := 2 ^ (Nat.log2 a / 2)

/-- The heuristic greatest common divisor at `n + 1` variables, given one at `n`: evaluate
the last variable at a large integer, take the greatest common divisor of the values, and
read a candidate off its digits; the candidate is kept if it divides both. -/
def heu (n : Nat) (gcdLow : ZP n → ZP n → ZP n) (p q : ZP (n + 1)) : Option (ZP (n + 1)) :=
  let cp := icont (n + 1) p
  let cq := icont (n + 1) q
  let c := Nat.gcd cp cq
  let p := divInt (n + 1) p c
  let q := divInt (n + 1) q c
  let np := maxAbs (n + 1) p
  let nq := maxAbs (n + 1) q
  let b := 2 * min np nq + 29
  let lp := (leadInt (n + 1) p).natAbs
  let lq := (leadInt (n + 1) q).natAbs
  let x0 := max (min b (99 * isqrt b)) (2 * min (np / max lp 1) (nq / max lq 1) + 4)
  let deg := (toList p).length + (toList q).length
  go p q c deg 6 x0
where
  go (p q : ZP (n + 1)) (c deg : Nat) : Nat → Nat → Option (ZP (n + 1))
    | 0, _ => none
    | fuel + 1, x =>
      if Nat.log2 x * deg > 20000 then none
      else
        let pp := evalLast n p x
        let qq := evalLast n q x
        let next := 73794 * x * isqrt (isqrt x) / 27011
        if isZero n pp || isZero n qq then go p q c deg fuel next
        else
          let h := primZ (n + 1) (interpolate n (gcdLow pp qq) x)
          if beq (n + 1) h (one (n + 1)) then some (const (n + 1) c)
          else
            match divExact? (n + 1) p h, divExact? (n + 1) q h with
            | some _, some _ => some (smul (n + 1) c h)
            | _, _ => go p q c deg fuel next

/-- The content in the last variable, a greatest common divisor of the coefficients, and
the polynomial divided by it. -/
def contPrim (n : Nat) (gcdLow : ZP n → ZP n → ZP n) (p : List (ZP n)) :
    ZP n × List (ZP n) :=
  let c := p.foldl (fun g e => gcdLow g e) (zero n)
  if isZero n c || beq n c (one n) then (one n, p)
  else
    match p.mapM fun e => divExact? n e c with
    | some q => (c, q)
    | none => (one n, p)

/-- The primitive Euclidean algorithm in the last variable. -/
def prs (n : Nat) (gcdLow : ZP n → ZP n → ZP n) (p q : ZP (n + 1)) : ZP (n + 1) :=
  let a := contPrim n gcdLow (toList p)
  let b := contPrim n gcdLow (toList q)
  let c := gcdLow a.1 b.1
  let h := if a.2.length ≥ b.2.length then go (a.2.length + b.2.length + 2) a.2 b.2
    else go (a.2.length + b.2.length + 2) b.2 a.2
  fixSign (n + 1) (mul (n + 1) (ofList [c]) (ofList h))
where
  go : Nat → List (ZP n) → List (ZP n) → List (ZP n)
    | 0, a, _ => a
    | fuel + 1, a, b =>
      if b.isEmpty then a
      else
        let r := premL n b (a.length + 1) a
        if r.isEmpty then b
        else if r.length == 1 then [one n]
        else go fuel b (contPrim n gcdLow r).2

/-- A greatest common divisor with positive leading integer coefficient. -/
def gcd : (n : Nat) → ZP n → ZP n → ZP n
  | 0, a, b => ofInt (Int.gcd (toInt a) (toInt b))
  | n + 1, p, q =>
    if isZero (n + 1) p then fixSign (n + 1) q
    else if isZero (n + 1) q then fixSign (n + 1) p
    else if (toList p).length == 1 || (toList q).length == 1 then
      let a := (contPrim n (gcd n) (toList p)).1
      let b := (contPrim n (gcd n) (toList q)).1
      fixSign (n + 1) (ofList [gcd n a b])
    else
      match heu n (gcd n) p q with
      | some h => h
      | none => prs n (gcd n) p q

/-! ### Fractions -/

/-- A numerator and a denominator. -/
abbrev Frac (n : Nat) := ZP n × ZP n

def isOne (n : Nat) (p : ZP n) : Bool := beq n p (one n)

/-- The denominator with positive leading integer coefficient. -/
def fixFrac (n : Nat) (f : Frac n) : Frac n :=
  if leadInt n f.2 < 0 then (neg n f.1, neg n f.2) else f

/-- Divide both by their greatest common divisor. -/
def cancel (n : Nat) (a b : ZP n) : Frac n :=
  if isZero n a then (zero n, one n)
  else if isOne n b then (a, b)
  else
    let g := gcd n a b
    if isOne n g then fixFrac n (a, b)
    else
      match divExact? n a g, divExact? n b g with
      | some a', some b' => fixFrac n (a', b')
      | _, _ => fixFrac n (a, b)

def negF (n : Nat) (f : Frac n) : Frac n := (neg n f.1, f.2)

/-- The sum of two reduced fractions, reduced. -/
def addF (n : Nat) (f g : Frac n) : Frac n :=
  let (a, b) := f
  let (c, d) := g
  if isZero n a then g
  else if isZero n c then f
  else if isOne n b && isOne n d then (add n a c, b)
  else if isOne n b then (add n (mul n a d) c, d)
  else if isOne n d then (add n a (mul n c b), b)
  else if beq n b d then cancel n (add n a c) b
  else
    let e := gcd n b d
    if isOne n e then (add n (mul n a d) (mul n c b), mul n b d)
    else
      match divExact? n b e, divExact? n d e with
      | some b', some d' =>
        let t := add n (mul n a d') (mul n c b')
        if isZero n t then (zero n, one n)
        else
          let e2 := gcd n t e
          match divExact? n t e2, divExact? n d e2 with
          | some t', some d2 => fixFrac n (t', mul n b' d2)
          | _, _ => cancel n t (mul n b' d)
      | _, _ => cancel n (add n (mul n a d) (mul n c b)) (mul n b d)

/-- `a / d` with the common divisor cancelled. -/
def cancelPair (n : Nat) (a d : ZP n) : ZP n × ZP n :=
  if isOne n d then (a, d)
  else
    let g := gcd n a d
    if isOne n g then (a, d)
    else
      match divExact? n a g, divExact? n d g with
      | some a', some d' => (a', d')
      | _, _ => (a, d)

/-- The product of two reduced fractions, reduced. -/
def mulF (n : Nat) (f g : Frac n) : Frac n :=
  let (a, b) := f
  let (c, d) := g
  if isZero n a || isZero n c then (zero n, one n)
  else if isOne n b && isOne n d then (mul n a c, b)
  else
    let ad := cancelPair n a d
    let cb := cancelPair n c b
    fixFrac n (mul n ad.1 cb.1, mul n cb.2 ad.2)

/-- The quotient of two reduced fractions, reduced; zero when the divisor is zero. -/
def divF (n : Nat) (f g : Frac n) : Frac n :=
  if isZero n g.1 then (zero n, one n) else mulF n f (fixFrac n (g.2, g.1))

/-- A term as a reduced fraction. -/
def toFrac (n : Nat) : Term n → Frac n
  | .const q => (const n q.num, const n q.den)
  | .gen i => (var n i, one n)
  | .neg a => negF n (toFrac n a)
  | .add a b => addF n (toFrac n a) (toFrac n b)
  | .sub a b => addF n (toFrac n a) (negF n (toFrac n b))
  | .mul a b => mulF n (toFrac n a) (toFrac n b)
  | .div a b => divF n (toFrac n a) (toFrac n b)

/-! ### Back to terms -/

/-- `a + b`, dropping a vanishing constant. -/
def tadd {N : Nat} (a b : Term N) : Term N :=
  match a with
  | .const q => if q == 0 then b else .add a b
  | _ => .add a b

/-- `θ b`, dropping a factor one. -/
def tmul {N : Nat} (θ b : Term N) : Term N :=
  match b with
  | .const q => if q == 1 then θ else .mul θ b
  | _ => .mul θ b

/-- Horner's form `c₀ + θ (c₁ + θ (…))`. -/
def hornerT {N : Nat} {α : Type} (θ : Term N) (f : α → Term N) : List α → Term N
  | [] => .const 0
  | c :: cs => if cs.isEmpty then f c else tadd (f c) (tmul θ (hornerT θ f cs))

/-- A polynomial in the first `n` generators as a term of depth `N`. -/
def ofZPAt (N : Nat) : (n : Nat) → n ≤ N → ZP n → Term N
  | 0, _, a => .const (toInt a)
  | n + 1, h, p => hornerT (.gen ⟨n, by omega⟩) (ofZPAt N n (by omega)) (toList p)

def ofZP (n : Nat) (p : ZP n) : Term n := ofZPAt n n (Nat.le_refl n) p

/-- Lowest terms: a quotient of two polynomials with integer coefficients without a common
divisor, the denominator with positive leading integer coefficient. -/
def normFF {n : Nat} (e : Term n) : Term n :=
  let f := toFrac n e
  if isConst n f.2 then
    let d := leadInt n f.2
    if isConst n f.1 then .const ((leadInt n f.1 : Rat) / d)
    else if d == 1 then ofZP n f.1 else .div (ofZP n f.1) (.const d)
  else .div (ofZP n f.1) (ofZP n f.2)

end ZP

end SympyProofs.Calculus.Risch
