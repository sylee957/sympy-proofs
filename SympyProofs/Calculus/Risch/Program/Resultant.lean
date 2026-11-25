module

public import SympyProofs.Calculus.Risch.Program.Constraints
public import SympyProofs.Calculus.Risch.Program.Poly

/-! The resultant of `B` and `N - z E` as a polynomial in `z`, and a bound on the natural
numbers that are roots of a polynomial over the field of a tower. The resultant is computed
by the subresultant algorithm over the field one level up, in which `z` is a generator, and
converted back into a polynomial in `z`. A natural number
that is a root of a polynomial over the field is a root of each of its rational slices, and
the roots of a rational polynomial are bounded by Cauchy's estimate. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Resultant

/-- `x ^ j` for a term. -/
def tpow (x : Term n) : Nat → Term n
  | 0 => .const 1
  | j + 1 => Coeff.mul x (tpow x j)

/-- The subresultant algorithm of Collins and Brown, over the field of depth `n`. For `A`
and `B` with nonzero highest coefficients and `deg A ≥ deg B`, the result is
`Res(A, B) g^(-deg B) h^(1 - deg A)`. A step replaces `(A, B)` by `(B, R / (g h^δ))`, where
`δ = deg A - deg B` and `R` is the pseudo-remainder of `A` by `B`, and then sets `g` to the
highest coefficient `b` of `B` and `h` to `h^(1-δ) b^δ`. When `B` is a constant `b`, the
result is `h^(1 - deg A) b^(deg A)`. The divisions are exact, so the coefficients stay
polynomial in the generators of the field, but the result does not rely on this. -/
def subresLoop : Nat → Poly n → Poly n → Term n → Term n → Term n
  | 0, _, _, _, _ => .const 0
  | fuel + 1, A, B, g, h =>
    let m := A.length - 1
    let d := B.length - 1
    let b := Poly.lead B
    if d == 0 then Term.norm (Coeff.div (Coeff.mul h (tpow b m)) (tpow h m))
    else
      let δ := m - d
      let R := Poly.trim (Poly.rem (Poly.scale (tpow b (δ + 1)) A) B)
      if R.isEmpty then .const 0
      else
        let β := Coeff.mul g (tpow h δ)
        let r := subresLoop fuel B (Poly.norm (R.map fun c => .div c β)) b
          (Term.norm (Coeff.div (Coeff.mul h (tpow b δ)) (tpow h δ)))
        if m * d % 2 == 1 then Coeff.neg r else r

/-- The resultant of two polynomials over the field of depth `n`, with their degrees as the
formal degrees. -/
def subresultant (F G : Poly n) : Term n :=
  let F := Poly.trim F
  let G := Poly.trim G
  if F.isEmpty then (if Nat.ble G.length 1 then .const 1 else .const 0)
  else if G.isEmpty then (if Nat.ble F.length 1 then .const 1 else .const 0)
  else if Nat.ble G.length F.length then subresLoop G.length F G (.const 1) (.const 1)
  else
    let r := subresLoop F.length G F (.const 1) (.const 1)
    if (F.length - 1) * (G.length - 1) % 2 == 1 then Coeff.neg r else r

/-- The resultant of `B` and `N - z E` as polynomials in the generator, a polynomial in `z`.
It is computed by `subresultant` one level up, where the newest generator stands for `z`. -/
def resPoly (N B E : Poly n) : Poly n :=
  let F : Poly (n + 1) := B.map Term.weaken
  let G : Poly (n + 1) :=
    Poly.sub (N.map Term.weaken) (Poly.scale (.gen (Fin.last n)) (E.map Term.weaken))
  let nd := Poly.ofTerm (subresultant F G)
  Poly.quot nd.1 (Poly.trim (Poly.norm nd.2))

/-- The coefficients of one monomial, as a rational polynomial in `z`. -/
def slice (μ : Mono n) (ws : List (MPoly n)) : List Rat := ws.map (MPoly.coeff μ)

/-- A monomial with a nonzero coefficient in some polynomial of the list. -/
def pick (ws : List (MPoly n)) : Option (Mono n) :=
  ws.findSome? fun w => (w.find? fun t => MPoly.coeff t.1 w != 0).map (·.1)

def absQ (q : Rat) : Rat := if Rat.blt q 0 then -q else q

/-- Remove vanishing coefficients of highest degree. -/
def trimQ : List Rat → List Rat
  | [] => []
  | c :: cs => if (trimQ cs).isEmpty then (if c == 0 then [] else [c]) else c :: trimQ cs

/-- Cauchy's estimate: an upper bound for the natural numbers that are roots of a nonzero
rational polynomial, given by its coefficients from degree zero. -/
def radius (p : List Rat) : Nat :=
  let q := trimQ p
  let lead := absQ (q.getLastD 1)
  let lower := (q.dropLast.map absQ).foldl (· + ·) 0
  (1 + lower / lead).ceil.toNat

/-- An upper bound for the natural numbers that are roots of a nonzero polynomial over the
field of a tower. -/
def rootBound (P : Poly n) : Nat :=
  match pick (numerators P).1 with
  | none => 0
  | some μ => radius (slice μ (numerators P).1)

/-- A bound on the natural numbers `j` for which some prime factor of `B` divides
`N - j E`. -/
def residueBound (N B E : Poly n) : Nat := rootBound (resPoly N B E)

end Resultant

end SympyProofs.Calculus.Risch
