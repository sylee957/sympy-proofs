module

public import SympyProofs.Calculus.Risch.Program.Solve
public import SympyProofs.Calculus.Risch.Program.Answer

/-! Integration of a polynomial in the newest generator, with negative powers at an
exponential step. The coefficients of the integral satisfy differential equations in the
preceding field. The constant term is integrated in the preceding field by `descend`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace PolyPart

open Poly

/-- Apply `step` to each entry with its index, starting from `k`. -/
def solveFrom (step : Nat → Term n → Option (Term n)) (k : Nat) : Poly n → Option (Poly n)
  | [] => some []
  | p :: ps =>
    match step k p, solveFrom step (k + 1) ps with
    | some q, some qs => some (q :: qs)
    | _, _ => none

/-- At an exponential step with exponent `u`: integrate `(Σ csᵢ θⁱ) / θᵏ`. The coefficient
`q` of `θʲ⁻ᵏ` in the integral satisfies `q′ + (j - k) u′ q = csⱼ` for `j ≠ k`. -/
def expPart (t : Tower n) (u : Term n) (descend : Term n → Result n) (cs : Poly n) (k : Nat) :
    Result (n + 1) :=
  match solveFrom (fun j c =>
      if j == k then some (.const 0)
      else rde t (.mul (.const ((j : Rat) - (k : Rat))) (t.D u)) c) 0 cs with
  | none => .nonelementary
  | some rs =>
    match descend (coeff cs k) with
    | .nonelementary => .nonelementary
    | .elementary a =>
      .elementary (a.weaken.addField (.div (toTerm rs) (Term.genPow n k)))

/-- At a primitive step with `θ′ = b`: solve the triangular system for the coefficients of
the integral from the highest degree. The first component is the coefficient of the current
degree up to an undetermined constant, which is fixed by the equation one degree lower. -/
def primSolve (t : Tower n) (b : Term n) : Nat → Poly n → Option (Term n × Poly n)
  | _, [] => some (.const 0, [])
  | i, c :: cs =>
    match primSolve t b (i + 1) cs with
    | none => none
    | some (hi, Ps) =>
      match limited t (.sub c (.mul (.mul (.const ((i + 1 : Nat) : Rat)) b) hi)) b with
      | none => none
      | some (γ, v) => some (v, .add hi (.const (γ / ((i + 1 : Nat) : Rat))) :: Ps)

/-- At a primitive step: integrate the polynomial `Σ csᵢ θⁱ`. What remains of the constant
term is integrated in the preceding field. If it has no elementary integral there, a
multiple of `b` may still be subtracted when `b` itself has none: the multiple is then
unique, and it is found here when the quotient is a rational number. -/
def primPart (t : Tower n) (b : Term n) (descend : Term n → Result n) (cs : Poly n) :
    Result (n + 1) :=
  match primSolve t b 1 cs.tail with
  | none => .nonelementary
  | some (v, Ps) =>
    let g := Term.sub (coeff cs 0) (.mul b v)
    match descend g with
    | .elementary a => .elementary (a.weaken.addField (toTerm (.const 0 :: v :: Ps)))
    | .nonelementary =>
      match descend b with
      | .elementary _ => .nonelementary
      | .nonelementary =>
        match Term.scalar? (.div g b) with
        | none => .nonelementary
        | some c => .elementary ⟨toTerm (.const 0 :: .add v (.const c) :: Ps), []⟩

/-- Integrate `(Σ csᵢ θⁱ) / θᵏ`, where `k = 0` at a primitive step. -/
def polyPart : Tower (n + 1) → (Term n → Result n) → Poly n → Nat → Result (n + 1)
  | .prim t b, descend, cs, _ => primPart t b descend cs
  | .exp t u, descend, cs, k => expPart t u descend cs k

end PolyPart

end SympyProofs.Calculus.Risch
