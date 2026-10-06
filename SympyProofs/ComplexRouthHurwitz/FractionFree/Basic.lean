import SympyProofs.ComplexRouthHurwitz.Reference.Basic

/-! Previous-squared-pivot field model, using fixed-width coefficient vectors. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

/-- A Gaussian unit makes the leading real part positive without coefficient growth. -/
def phase (z : ℂ) : ℂ :=
  if z.re = 0 then (if z.im < 0 then Complex.I else -Complex.I)
  else if z.re < 0 then -1 else 1

/-- The degree-zero first elimination; a real leading coefficient needs only a scan. -/
def initialRows {N} (a : Coefficients.Row N) (n : ℕ) : Coefficients.Pair N :=
  let r := Coefficients.scan a n
  let z := Coefficients.entry a n
  { upper := r.upper, lower := if z.im = 0 then r.lower else
      Vector.ofFn (fun j => (z.re : ℂ)*r.lower[j] - (z.im : ℂ)*Complex.I*r.upper[j]) }

def initialDivisor {N} (a : Coefficients.Row N) (n : ℕ) : ℝ :=
  let z := Coefficients.entry a n
  if z.im = 0 then 1 else z.re

/-- Coordinatewise pseudo-remainder divided exactly by the stored divisor. -/
def nextLower {N : ℕ} (d : ℕ) (D : ℝ) (u v : Coefficients.Row N) : Coefficients.Row N :=
  let A := (Coefficients.entry u (d+1)).re
  let B := (Coefficients.entry v d).re
  let γ := (B:ℂ)*Coefficients.entry u d - (A:ℂ)*Coefficients.entry v (d-1)
  Vector.ofFn (fun j => ((B:ℂ)^2*u[j] - γ*v[j] - (A:ℂ)*(B:ℂ)*
      (if j.val = 0 then 0 else Coefficients.entry v (j.val-1))) / (D:ℂ))

/-- Previous-squared-pivot field model. Repairs restart the divisor at one.
The Gaussian runner in `Exact` realizes this field model in its coefficient ring;
its separate determinant invariant certifies all reached divisions. -/
def runFF (p : ℂ[X]) : Result (p.natDegree+1) := Id.run do
  let n := p.natDegree
  let unit := phase p.leadingCoeff
  let coefficients := Vector.ofFn (fun j : Fin (n+1) => unit * p.coeff j.val)
  if n = 0 then
    return { rows := [coefficients], pivots := [], rightRoots := 0, axisRoots := 0, stable := true }
  else
    let initial := initialRows coefficients n
    let mut upper := initial.upper
    let mut lower := initial.lower
    let mut rows := []
    let mut pivots : List ℝ := []
    let mut count := 0
    let mut auxiliary : Option Auxiliary := none
    let mut divisor : ℝ := initialDivisor coefficients n
    for k in List.range n do
      let d := n-(k+1)
      auxiliary := if lower = Coefficients.zero (n+1) ∧ auxiliary.isNone then
        some { degree := d+1, rightBefore := count } else auxiliary
      divisor := if (Coefficients.entry lower d).re = 0 then 1 else divisor
      let r := Coefficients.repair d upper lower
      rows := rows ++ [r.upper, r.lower]
      let pivot := (Coefficients.entry r.lower d).re
      pivots := pivots ++ [pivot]
      count := count + if (Coefficients.entry r.upper (d+1)).re < 0 ↔ pivot < 0 then 0 else 1
      if d = 0 then
        upper := Coefficients.one (n+1)
        lower := Coefficients.zero (n+1)
      else
        upper := r.lower
        lower := nextLower d divisor r.upper r.lower
      divisor := pivot^2
    let axis := axisTotal auxiliary count
    return {
      rows := rows, pivots := pivots, rightRoots := count, axisRoots := axis,
      stable := decide (count = 0 ∧ axis = 0) }


end
end RouthHurwitz.ComplexRouth.FractionFree
