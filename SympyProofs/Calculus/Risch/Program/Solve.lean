module

public import SympyProofs.Calculus.Risch.Program.Rel
public import SympyProofs.Calculus.Risch.Program.Resultant

/-! Part (b) of Risch's Main Theorem: all solutions `y` in the field of a tower, with
constants `cᵢ`, of `y′ + f y = Σ cᵢ gᵢ`. The result is a list of field elements `hⱼ` and a
linear system over the rationals: the solutions are the `y = Σ dⱼ hⱼ` for which `(c, d)`
solves the system.

At a tower step the equation is cleared to `R Y′ + S Y = Σ cᵢ Gᵢ` for a polynomial `Y` in
the newest generator, using a common denominator for all solutions. A bound on the degree of
`Y` is found, and then its coefficients are determined from the highest downwards, each
from an equation of the same kind in the preceding field. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Solve

open Poly

/-- The operator `Y ↦ R Y′ + S Y` on coefficient lists. -/
def applyL (t : Tower (n + 1)) (R S Y : Poly n) : Poly n := add (mul R (der t Y)) (mul S Y)

/-- The coefficients of degree `j` of a list of polynomials. -/
def coeffs (Gs : List (Poly n)) (j : Nat) : List (Term n) := Gs.map fun G => coeff G j

def maxLen (Gs : List (Poly n)) : Nat := Gs.foldr (fun G m => max G.length m) 0

/-- Equations on the first `Gs.length` parameters making every coefficient of degree at
least `lo` of the combination vanish. -/
def vanish (Gs : List (Poly n)) (lo hi : Nat) : List (List Rat) :=
  (List.range (hi - lo)).flatMap fun i =>
    (rowsOf (coeffs Gs (lo + i))).map fun r => r.take Gs.length

/-- Add the first list to the front of the second, entry by entry. -/
def addFront : List (Poly n) → List (Poly n) → List (Poly n)
  | [], Ys => Ys
  | _ :: _, [] => []
  | m :: ms, Y :: Ys => add Y m :: addFront ms Ys

/-- A combination of polynomials with rational coefficients. -/
def lcomb : List Rat → List (Poly n) → Poly n
  | c :: v, Y :: Ys => add (scale (.const c) Y) (lcomb v Ys)
  | _, _ => []

/-- Replace the parameters by the generators of the solution space of the constraints `Cs`
before continuing with `rec`. -/
def restrict (Cs : List (List Rat)) (Gs : List (Poly n))
    (rec : List (Poly n) → List (Poly n) × List (List Rat)) : List (Poly n) × List (List Rat) :=
  let G := Linear.kernel Cs Gs.length
  let out := rec (G.map fun v => norm (lcomb v Gs))
  (Gs.map (fun _ => ([] : Poly n)) ++ out.1,
    (List.range Gs.length).map
        (fun i => Linear.unit Gs.length i ++ G.map fun v => -(v.getD i 0)) ++
      out.2.map fun r => List.replicate Gs.length 0 ++ r)

/-- Solve `R Y′ + S Y = Σ pᵢ Gᵢ` for polynomials `Y` with fewer than `k` coefficients, given
the solver `lower` of the preceding field. The result lists one polynomial for each
parameter, old and new, and equations on the parameters. -/
def solvePoly (t : Tower (n + 1))
    (lower : Term n → List (Term n) → List (Term n) × List (List Rat)) (R S : Poly n)
    (lam : Nat) : Nat → List (Poly n) → List (Poly n) × List (List Rat)
  | 0, Gs => (Gs.map fun _ => [], vanish Gs 0 (maxLen Gs))
  | k + 1, Gs =>
    let r := coeff R lam
    let s := Term.add (coeff S lam) (.mul (.mul (.const (k : Rat)) t.twist) r)
    let high := vanish Gs (lam + k + 1) (maxLen Gs)
    if r.isZero then
      let η := fun G : Poly n => Term.norm (.div (coeff G (lam + k)) s)
      let rec' := restrict high
        (Gs.map fun G => norm (sub G (applyL t R S (mono k (η G)))))
        (fun Gs' => solvePoly t lower R S lam k Gs')
      (addFront ((Gs.map η).map (mono k)) rec'.1, rec'.2)
    else
      let sol := lower (Term.norm (.div s r))
        ((coeffs Gs (lam + k)).map fun g => Term.norm (.div g r))
      let rec' := restrict (high ++ sol.2.map fun row => row.take (Gs.length + sol.1.length))
        (Gs ++ sol.1.map fun h => norm (neg (applyL t R S (mono k h))))
        (fun Gs' => solvePoly t lower R S lam k Gs')
      (addFront (Gs.map (fun _ => ([] : Poly n)) ++ sol.1.map (mono k)) rec'.1, rec'.2)

/-- Powers of a polynomial. -/
def ppow (B : Poly n) : Nat → Poly n
  | 0 => [.const 1]
  | m + 1 => mul (ppow B m) B

/-- A bound for the order of an exponential generator in the denominator of a solution.
A primitive generator is not a special place. -/
def special : Tower (n + 1) → Poly n → Poly n → Poly n → Nat
  | .prim _ _, _, _, _ => 0
  | .exp t u, N, B, T =>
    max T.length (if (coeff B 0).isZero then 0
      else Rel.exponentBound t u (.neg (.div (coeff N 0) (coeff B 0))))

/-- The polynomial data of one instance: `f = N/B` in lowest terms, the right-hand sides
`Ws/T`, a denominator `P` for every solution, and the cleared equation
`R Y′ + S Y = Σ cᵢ Gᵢ` with coefficients of degree at most `lam`. -/
structure Pieces (n : Nat) where
  N : Poly n
  B : Poly n
  T : Poly n
  P : Poly n
  R : Poly n
  S : Poly n
  Ws : List (Poly n)
  Gs : List (Poly n)
  lam : Nat

/-- The instance `y′ + f y = Σ cᵢ gᵢ` cleared of denominators, read off `f` and `gs` as
they are written. -/
def piecesOf (t : Tower (n + 1)) (f : Term (n + 1)) (gs : List (Term (n + 1))) : Pieces n :=
  let red := reduce (ofTerm f).1 (ofTerm f).2
  let N := norm red.1
  let B := trim (norm red.2)
  let cm := commonDen gs
  let T := norm cm.2
  let Ws := cm.1.map norm
  let P := norm (mul (mono (special t N B T) (.const 1))
    (mul T (ppow B (Resultant.residueBound N B (der t B)))))
  let R := trim (norm (mul P (mul B T)))
  let S := trim (norm (mul T (sub (mul N P) (mul B (der t P)))))
  let E := norm (mul (mul P P) B)
  ⟨N, B, T, P, R, S, Ws, Ws.map (fun W => norm (mul W E)), max (R.length - 1) (S.length - 1)⟩

/-- The instance cleared of denominators, from `f` and `gs` in lowest terms. A term as
written may carry denominators that cancel, and each would raise the bounds on the
denominator and the degree of the solutions. -/
def pieces (t : Tower (n + 1)) (f : Term (n + 1)) (gs : List (Term (n + 1))) : Pieces n :=
  piecesOf t (Term.norm f) (gs.map Term.norm)

/-- The element whose primitive, up to a multiple of the derivative of a primitive
generator, governs cancellation of the two highest coefficients. -/
def cancelQ (R S : Poly n) (lam : Nat) : Term n :=
  .div (.sub (.mul (if lam == 0 then .const 0 else coeff R (lam - 1)) (coeff S lam))
      (.mul (coeff R lam) (if lam == 0 then .const 0 else coeff S (lam - 1))))
    (.mul (coeff R lam) (coeff R lam))

/-- The natural number `a`, if any, such that `Q - a b` has a primitive in the preceding
field, read off the solutions of `y′ = c₁ Q + c₂ b`. -/
def third (lower : Term n → List (Term n) → List (Term n) × List (List Rat)) (b Q : Term n) :
    Nat :=
  let sol := lower (.const 0) [Q, b]
  match Linear.normalized sol.2 (2 + sol.1.length) with
  | some (_ :: c :: _) => if (-c).den == 1 then (-c).num.toNat else 0
  | _ => 0

/-- A strict bound on the degree of every polynomial solution. -/
def degBound : Tower (n + 1) → (Term n → List (Term n) → List (Term n) × List (List Rat)) →
    Poly n → Poly n → Nat → List (Poly n) → Nat
  | .prim _ b, lower, R, S, lam, Gs =>
    if (coeff R lam).isZero then maxLen Gs + 2
    else max (maxLen Gs + 2) (third lower b (cancelQ R S lam) + 1)
  | .exp t u, _, R, S, lam, Gs =>
    if (coeff R lam).isZero then maxLen Gs
    else max (maxLen Gs) (Rel.exponentBound t u (.div (coeff S lam) (coeff R lam)) + 1)

/-- One basis element for each generator of the solution space of the system. `mix v` is a
term for the combination of the old basis with coefficients `v`. -/
def compress (m size : Nat) (rows : List (List Rat)) (mix : List Rat → Term n) :
    List (Term n) × List (List Rat) :=
  let G := Linear.kernel rows (m + size)
  (G.map fun v => mix (v.drop m),
    (List.range m).map fun i => Linear.unit m i ++ G.map fun v => -(v.getD i 0))

/-- Part (b) at a tower step, given the solver of the preceding field. -/
def stepSolve (t : Tower (n + 1))
    (lower : Term n → List (Term n) → List (Term n) × List (List Rat)) (f : Term (n + 1))
    (gs : List (Term (n + 1))) : List (Term (n + 1)) × List (List Rat) :=
  let pc := pieces t f gs
  let out := solvePoly t lower pc.R pc.S pc.lam (degBound t lower pc.R pc.S pc.lam pc.Gs) pc.Gs
  compress gs.length out.1.length
    ((List.range gs.length).map
        (fun i => Linear.unit gs.length i ++ (Linear.unit gs.length i).map fun q => -q) ++
      out.2.map fun r => List.replicate gs.length 0 ++ r)
    fun v => Term.norm (.div (toTerm (lcomb v out.1)) (toTerm pc.P))

/-- Part (b) over the constants, where the derivation vanishes: `f y = Σ cᵢ gᵢ`. -/
def constSolve (f : Term 0) (gs : List (Term 0)) : List (Term 0) × List (List Rat) :=
  ([.const 1], [gs.map (fun g => -g.evalRat) ++ [f.evalRat]])

/-- A combination of terms with rational coefficients. -/
def lincomb : List Rat → List (Term n) → Term n
  | c :: cs, h :: hs => .add (.mul (.const c) h) (lincomb cs hs)
  | _, _ => .const 0

end Solve

/-- Part (b) of the Main Theorem: a basis and a linear system for the solutions of
`y′ + f y = Σ cᵢ gᵢ` in the field of the tower. -/
def solve : {n : Nat} → Tower n → Term n → List (Term n) → List (Term n) × List (List Rat)
  | _, .const, f, gs => Solve.constSolve f gs
  | _, .prim t b, f, gs => Solve.stepSolve (.prim t b) (solve t) f gs
  | _, .exp t u, f, gs => Solve.stepSolve (.exp t u) (solve t) f gs

/-- A solution of `y′ + a y = h` in the field of the tower, if there is one. -/
def rde (t : Tower n) (a h : Term n) : Option (Term n) :=
  let sol := solve t a [h]
  match Linear.normalized sol.2 (1 + sol.1.length) with
  | some (_ :: d) => some (Solve.lincomb d sol.1)
  | _ => none

/-- A rational `c` and an element `v` of the field with `v′ = g - c b`, if there are any. -/
def limited (t : Tower n) (g b : Term n) : Option (Rat × Term n) :=
  let sol := solve t (.const 0) [g, b]
  match Linear.normalized sol.2 (2 + sol.1.length) with
  | some (_ :: c :: d) => some (-c, Solve.lincomb d sol.1)
  | _ => none

end SympyProofs.Calculus.Risch
