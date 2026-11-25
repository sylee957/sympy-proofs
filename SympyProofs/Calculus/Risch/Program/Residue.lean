module

public import SympyProofs.Calculus.Risch.Program.Resultant
public import SympyProofs.Calculus.Risch.Program.Hermite
public import SympyProofs.Calculus.Risch.Program.Answer

/-! The logarithmic part of a fraction `A / D` with squarefree denominator and normal prime
factors (Risch 1969, pp. 181–182).

The residues are the constants `c` for which `A - c D′` and `D` have a common factor: the
constant roots of the resultant `R(z)` of `A - z D′` and `D`. A constant is a root of `R`
exactly when it is a root of every rational slice of `R`, so the constant roots are the
roots of the greatest common divisor `r` of the slices, a polynomial with rational
coefficients.

The logarithm with coefficient `c` has argument `gcd(A - c D′, D)`. It is computed once for
all roots by the Euclidean algorithm with `z` a root of `r`, that is, with coefficients
polynomial in `z` modulo `r`. When a leading coefficient is neither zero nor invertible
modulo `r`, the modulus is split into the factor on which it vanishes and the factor on
which it is invertible, and the computation continues on each.

An elementary integral exists only if the greatest common divisors account for all of `D`:
the sum over the pieces of (number of roots) × (degree of the divisor) is the degree of
`D`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Residue

open Poly

/-- A polynomial in the generator whose coefficients are polynomials in the root `z`. -/
abbrev BPoly (n : Nat) := List (Poly n)

/-- A polynomial in `z` reduced modulo `m`, without vanishing leading coefficients. -/
def zred (m p : Poly n) : Poly n := trim (norm (rem p m))

def zmul (m p q : Poly n) : Poly n := zred m (mul p q)

/-- Reduce every coefficient modulo `m` and remove the vanishing ones of highest degree. -/
def btrim (m : Poly n) : BPoly n → BPoly n
  | [] => []
  | c :: cs =>
    if (btrim m cs).isEmpty then (if (zred m c).isEmpty then [] else [zred m c])
    else zred m c :: btrim m cs

/-- `a - b` modulo `m`, coefficient by coefficient. -/
def bsub (m : Poly n) : BPoly n → BPoly n → BPoly n
  | [], q => q.map fun c => zred m (neg c)
  | p, [] => p
  | a :: p, b :: q => zred m (sub a b) :: bsub m p q

/-- Pieces of the modulus on each of which `p` is zero or has leading coefficient one. -/
def normalize : Nat → Poly n → BPoly n → List (Poly n × BPoly n)
  | 0, m, p => [(m, btrim m p)]
  | fuel + 1, m, p =>
    let p' := btrim m p
    match p'.getLast? with
    | none => [(m, [])]
    | some l =>
      let h := gcd l m
      let hh := trim (norm h.1)
      if Nat.ble hh.length 1 then
        let inv := zred m (Hermite.scaleInv (coeff hh 0) h.2.1)
        [(m, p'.map (zmul m inv))]
      else normalize fuel hh p' ++ normalize fuel (trim (norm (quot m hh))) p'

/-- The remainder of `a` on division by `b`, which has leading coefficient one modulo `m`. -/
def bremMonic (m : Poly n) (b : BPoly n) : Nat → BPoly n → BPoly n
  | 0, a => a
  | fuel + 1, a =>
    if Nat.blt a.length b.length then a
    else
      let c := a.getLastD []
      bremMonic m b fuel
        (bsub m a (List.replicate (a.length - b.length) [] ++ b.map (zmul m c))).dropLast

/-- The Euclidean algorithm modulo `m`, splitting the modulus where necessary. Each piece
is a factor of the modulus with a greatest common divisor of `a` and `b` valid at its
roots. -/
def gcdMod : Nat → Poly n → BPoly n → BPoly n → List (Poly n × BPoly n)
  | 0, m, a, _ => [(m, a)]
  | fuel + 1, m, a, b =>
    (normalize m.length m b).flatMap fun piece =>
      if piece.2.isEmpty then normalize piece.1.length piece.1 a
      else gcdMod fuel piece.1 piece.2 (bremMonic piece.1 piece.2 a.length a)

/-- The squarefree polynomial with rational coefficients whose roots are the constant roots
of `R`. -/
def constRoots (R : Poly n) : Poly 0 :=
  let ws := (numerators R).1
  let slices : List (Poly 0) :=
    (monomials ws).map fun μ => ws.map fun w => Term.const (MPoly.coeff μ w)
  let g := slices.foldl (fun g s => trim (norm (gcd g s).1)) []
  trim (norm (quot g (trim (norm (gcd g (formalD g)).1))))

/-- `A - z E` and `D` as polynomials in the generator with coefficients polynomial in `z`. -/
def shifted : Poly n → Poly n → BPoly n
  | [], E => E.map fun e => [.const 0, Coeff.neg e]
  | A, [] => A.map fun a => [a]
  | a :: A, e :: E => [a, Coeff.neg e] :: shifted A E

/-- The logarithmic part of `A / D`: pieces `(m, g)` standing for the sum over the roots
`c` of `m` of `c log g(c)`, and the constant by which `A / D` differs from the derivative of
these sums. `none` when the fraction has no elementary integral. -/
def logPart (t : Tower (n + 1)) (A D : Poly n) : Option (List (Poly n × BPoly n) × Term n) :=
  if Nat.ble D.length 1 then some ([], .const 0)
  else
    let r : Poly n := (constRoots (Resultant.resPoly A D (der t D))).map fun c => .const c.evalRat
    let pieces :=
      if Nat.ble r.length 1 then []
      else (gcdMod (D.length + 1) r (shifted A (der t D)) (D.map fun c => [c])).filter
        fun piece => !Nat.ble piece.2.length 1
    let total := pieces.foldl (fun s piece => s + (piece.1.length - 1) * (piece.2.length - 1)) 0
    if total == D.length - 1 then
      some (pieces, Coeff.mul (pieces.foldl (fun s piece =>
        Coeff.add s (Coeff.mul (.const ((piece.2.length - 1 : Nat) : Rat))
          (.div (coeff piece.1 (piece.1.length - 2)) (lead piece.1)))) (.const 0)) t.twist)
    else none

/-- A polynomial in the root as a term of the next depth, where the newest generator stands
for the root. -/
def zterm : Poly n → Term (n + 1) := toTerm

/-- A piece as a sum of logarithms over the field of depth `n + 1`. -/
def toRootSum (piece : Poly n × BPoly n) : RootSum (n + 1) :=
  ⟨piece.1.map Term.weaken,
    -- generator `n` is the tower generator and generator `n + 1` the root
    (piece.2.foldr (fun c acc =>
        Term.add ((zterm c).rename (Fin.lastCases (Fin.last (n + 1)) fun i => i.castSucc.castSucc))
          (.mul (.gen (Fin.last n).castSucc) acc)) (.const 0))⟩

end Residue

end SympyProofs.Calculus.Risch
