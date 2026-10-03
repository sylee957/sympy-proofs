import SympyProofs.RouthHurwitz.Exact.Domain
import SympyProofs.RouthHurwitz.Imperative.Basic

/-! One-pass polynomial inequality certificates at the input polynomial's degree.
`A` may itself be a polynomial ring in one or many parameters. -/
namespace RouthHurwitz.Parametric
open Exact Imperative.Bounds

/-- The generated fraction-free rows and the expressions required to be positive.
Rows are scaled by the input leading coefficient before elimination. If a symbolic
pivot is zero, the returned table ends at that row. -/
structure Result (A : Type*) (W : ℕ) where
  rows : List (Vector A W)
  positive : List A
  deriving Repr, DecidableEq

/-- Interpret the inequalities at a parameter assignment; injectivity is not required. -/
def Result.Holds {A : Type*} [CommRing A] {W : ℕ} (result : Result A W)
    (f : A →+* ℝ) : Prop :=
  ∀ a ∈ result.positive, 0 < f a

variable {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A]

/-- Rows for the polynomial multiplied by its coefficient of degree `n`.
At a specialization of actual degree `n`, its leading coefficient is a square. -/
def initial (p : Polynomial A) (n parity : ℕ) : Vector A (width n) :=
  Vector.ofFn (fun j => if 2*j.val+parity ≤ n then
    p.coeff n * p.coeff (n-(2*j.val+parity)) else 0)

/-- Generate the declared-degree stability condition with one unsigned table pass.
The positive leading-coefficient square excludes degree drops and the zero polynomial. -/
def run (p : Polynomial A) : Result A (width p.natDegree) := Id.run do
  let n := p.natDegree
  let leadingSquare := p.leadingCoeff * p.leadingCoeff
  if n = 0 then
    return { rows := [initial p n 0], positive := [leadingSquare] }
  else
    let W := width n
    have hW : 0 < W := width_pos n
    let mut upper := initial p n 0
    let mut lower := initial p n 1
    let mut pivots := [lower[0]]
    let mut divisor := 1
    let mut nextDivisor := 1
    let mut rows := [upper, lower]
    for _ in List.range (n-1) do
      if lower[0] ≠ 0 then
        let row := Vector.ofFn (fun j : Fin W =>
          if h : j.val+1 < W then
            (lower[0] * upper[j.val+1] - upper[0] * lower[j.val+1]) / divisor
          else 0)
        divisor := nextDivisor
        nextDivisor := lower[0]
        pivots := pivots ++ [row[0]]
        rows := rows ++ [row]
        upper := lower
        lower := row
    return { rows := rows, positive := leadingSquare :: pivots }

end RouthHurwitz.Parametric
