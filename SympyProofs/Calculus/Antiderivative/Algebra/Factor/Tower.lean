module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Split
public import SympyProofs.Calculus.Antiderivative.Algebra.K.CommonDen

/-! Factoring over a rational function field by Kronecker substitution over its constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

namespace Factor

/-- Clear coefficient denominators one variable at a time. Starting with the exponents of
the main variable, prepend the exponents of each lower variable when it is exposed. -/
def clearTerms : {n : ℕ} → List (List ℕ × K R n) → List (List ℕ × K R 0)
  | 0, terms => terms
  | _ + 1, terms =>
    let (ps, _) := commonDen (terms.map Prod.snd)
    clearTerms ((terms.zip ps).flatMap fun ((m, _), p) =>
      p.coeffs.zipIdx.filterMap fun (a, i) => if a = 0 then none else some (i :: m, a))

/-- The radix of each digit exceeds the corresponding partial degree of the input.
Variables absent from all terms use radix one. -/
def radices {F : Type} (width : ℕ) (ts : List (List ℕ × F)) : List ℕ :=
  (List.range width).map fun i => ts.foldl (fun b t => max b (t.1[i]?.getD 0 + 1)) 1

/-- Append a highest digit to a little-endian mixed-radix expansion. -/
def placeDigits (bases m : List ℕ) (high : ℕ) : ℕ :=
  (bases.zip m).foldr (fun (b, i) k => i + b * k) high

/-- Kronecker substitution, with the first variable as the least significant digit. -/
def encode (bases m : List ℕ) : ℕ := placeDigits bases m 0

/-- Extract the specified low digits, retaining the high quotient. -/
def digits : List ℕ → ℕ → List ℕ × ℕ
  | [], k => ([], k)
  | b :: bs, k =>
    let (tail, high) := digits bs (k / b)
    (k % b :: tail, high)

/-- Substitute a power of one variable for each of the variables in the sparse input. -/
def substitute {F : Type} [Field F] [DecidableEq F] (bases : List ℕ)
    (ts : List (List ℕ × F)) : Poly F :=
  ts.foldl (fun p (m, a) => p + Poly.monomial (encode bases m) a) 0

/-- Follow the coefficient inclusions from a field embedding down to the constants. -/
def descend {F : Type} [Field F] : {k : ℕ} → (K R k →+* F) → (K R 0 →+* F)
  | 0, f => f
  | _ + 1, f => descend (f.comp K.lift)

/-- Prepend the lower parameters in ascending order to a list of remaining variables. -/
def parameters {F : Type} [Field F] [DecidableEq F] :
    {k : ℕ} → (K R k →+* F) → List (Poly F) → List (Poly F)
  | 0, _, vs => vs
  | _ + 1, f, vs => parameters (f.comp K.lift) (Poly.C (f K.gen) :: vs)

/-- Evaluate an exponent vector at the supplied variables. -/
def monomialValue {F : Type} [Field F] [DecidableEq F] : List (Poly F) → List ℕ → Poly F
  | x :: xs, i :: is => x ^ i * monomialValue xs is
  | _, _ => 1

/-- Reverse Kronecker substitution on a single term, preserving the main variable. -/
def decodeTerm {F G : Type} [Field F] [Field G] [DecidableEq G]
    (f : F →+* G) (vs : List (Poly G)) (bases : List ℕ) (e : ℕ) (a : F) : Poly G :=
  Poly.C (f a) * monomialValue vs (digits bases e).1

/-- Reverse the substitution on a polynomial by summing the decoded terms. -/
def decode {F G : Type} [Field F] [Field G] [DecidableEq F] [DecidableEq G]
    (f : F →+* G) (vs : List (Poly G)) (bases : List ℕ) (q : Poly F) : Poly G :=
  q.coeffs.zipIdx.foldl (fun r (a, i) =>
    if a = 0 then r else r + decodeTerm f vs bases i a) 0

/-- Return a subset product giving a proper divisor after reversing the substitution. -/
def subsetFactor {C F : Type} [Field C] [DecidableEq C] [Field F] [DecidableEq F]
    (decode : Poly C → Poly F) (p : Poly F) (acc : Poly C) :
    List (Poly C) → Option (Poly F)
  | [] =>
    let q := decode acc
    if proper p q then some q else none
  | a :: as =>
    (subsetFactor decode p acc as).orElse fun _ => subsetFactor decode p (acc * a) as

/-- A divisor of the cleared polynomial maps to a product of irreducible univariate factors.
Reversing the substitution and checking division rejects spurious subsets. -/
def towerDivisor [ConstantFactors (K R 0)] {n : ℕ} (p : Poly (K R n)) :
    Option (Poly (K R n)) :=
  let terms := clearTerms (p.coeffs.zipIdx.filterMap fun (a, i) =>
    if a = 0 then none else some ([i], a))
  let bases := radices (n + 1) terms
  let id := RingHom.id (K R n)
  let restore := decode (descend id) (parameters id [Poly.X]) bases
  subsetFactor restore p 1 (ConstantFactors.factors (substitute bases terms))

end Factor

/-- Monic irreducible factors over the flat field, with multiplicities.
At height zero use the constant-field factorization directly. -/
def factorTower [ConstantFactors (K R 0)] : {n : ℕ} → Poly (K R n) → List (Poly (K R n))
  | 0, p => ConstantFactors.factors p
  | _ + 1, p => Factor.split Factor.towerDivisor p.natDegree p

end SympyProofs.Calculus.Antiderivative
