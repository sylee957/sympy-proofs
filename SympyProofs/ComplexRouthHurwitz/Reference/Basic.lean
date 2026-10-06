import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Basic.Complex.Basic

/-! The direct complex table uses fixed-width coefficient vectors, in ascending
power order. Polynomial input is read once; all subsequent arithmetic is scalar. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

structure Auxiliary where
  degree : ℕ
  rightBefore : ℕ

def axisTotal (aux : Option Auxiliary) (count : ℕ) : ℕ :=
  aux.elim 0 (fun a => a.degree - 2*(count-a.rightBefore))

namespace Coefficients
abbrev Row (N : ℕ) := Vector ℂ N

/-- Zero extension is used only for shifted coefficient indices. -/
def entry {N : ℕ} (a : Row N) (j : ℕ) : ℂ := if h : j < N then a[j] else 0

def zero (N : ℕ) : Row N := Vector.ofFn (fun _ => 0)
def one (N : ℕ) : Row N := Vector.ofFn (fun j => if j.val = 0 then 1 else 0)
def add {N : ℕ} (a b : Row N) : Row N := Vector.ofFn (fun j => a[j]+b[j])
def scale {N : ℕ} (c : ℂ) (a : Row N) : Row N := Vector.ofFn (fun j => c*a[j])
def derivative {N : ℕ} (a : Row N) : Row N :=
  Vector.ofFn (fun j => entry a (j.val+1) * (j.val+1 : ℕ))
def eval {N : ℕ} (a : Row N) (z : ℂ) : ℂ := ∑ j : Fin N, a[j]*z^j.val

structure Pair (N : ℕ) where
  upper : Row N
  lower : Row N

/-- Split each coefficient into its alternating real and imaginary parts. -/
def scan {N : ℕ} (a : Row N) (n : ℕ) : Pair N := {
  upper := Vector.ofFn (fun j => if n%2 = j.val%2 then (a[j].re : ℂ) else a[j].im*Complex.I)
  lower := Vector.ofFn (fun j => if n%2 = j.val%2 then a[j].im*Complex.I else (a[j].re : ℂ)) }

def remainder {N : ℕ} (d : ℕ) (u v : Row N) : Row N :=
  let c : ℝ := (entry u (d+2)).re / (entry v (d+1)).re
  let b := (entry u (d+1) - (c : ℂ)*entry v d) / entry v (d+1)
  Vector.ofFn (fun j => u[j]-b*v[j]-(c : ℂ)*(if j.val = 0 then 0 else entry v (j.val-1)))

/-- At most 2(d+1)+1 distinct points suffice for the nonzero Wronskian. -/
def repairOffset {N : ℕ} (d : ℕ) (u v : Row N) : ℕ :=
  let du := derivative u
  let dv := derivative v
  ((List.range (2*(d+1)+1)).find? (fun j : ℕ =>
    let z := (j : ℂ)*Complex.I
    decide (eval u z * eval dv z - eval du z * eval v z ≠ 0))).getD 0

/-- Shift, reverse at the current degree, and normalize. The binomial sum is
computed directly from coefficients; the repair proof guarantees a nonzero normalization factor. -/
def reciprocal {N : ℕ} (a : Row N) (m : ℕ) (t : ℝ) : Row N :=
  let z := (t : ℂ)*Complex.I
  let factor := conj (eval a z)
  Vector.ofFn (fun i => if i.val ≤ m then
    (∑ j : Fin N, a[j] * (j.val.choose (m-i.val) : ℂ) * z^(j.val-(m-i.val))) * factor
    else 0)

def repair {N : ℕ} (d : ℕ) (u v : Row N) : Pair N :=
  if v = zero N then { upper := u, lower := derivative u }
  else if (entry v d).re = 0 then
    scan (reciprocal (add u v) (d+1) (repairOffset d u v)) (d+1)
  else { upper := u, lower := v }
end Coefficients

/-- Counts include multiplicities. Rows are repaired pairs of coefficient vectors,
all of the original width, with coefficient of s^j stored at index j. -/
structure Result (N : ℕ) where
  rows : List (Coefficients.Row N)
  pivots : List ℝ
  rightRoots : ℕ
  axisRoots : ℕ
  stable : Bool

/-- Unpack once, then run the entire table on fixed-width vectors.
Correctness requires nonzero input; this precondition belongs to the theorems. -/
def run (p : Polynomial ℂ) : Result (p.natDegree+1) := Id.run do
  let n := p.natDegree
  let lc := p.leadingCoeff
  let coefficients := Vector.ofFn (fun j : Fin (n+1) => p.coeff j.val * conj lc)
  if n = 0 then
    return {
      rows := [coefficients], pivots := [], rightRoots := 0,
      axisRoots := 0, stable := true }
  else
    let initial := Coefficients.scan coefficients n
    let mut upper := initial.upper
    let mut lower := initial.lower
    let mut rows := []
    let mut pivots : List ℝ := []
    let mut count := 0
    let mut auxiliary : Option Auxiliary := none
    for k in List.range n do
      let d := n-(k+1)
      auxiliary := if lower = Coefficients.zero (n+1) ∧ auxiliary.isNone then
        some { degree := d+1, rightBefore := count } else auxiliary
      let r := Coefficients.repair d upper lower
      rows := rows ++ [r.upper, r.lower]
      let pivot := (Coefficients.entry r.lower d).re
      pivots := pivots ++ [pivot]
      count := count + if (Coefficients.entry r.upper (d+1)).re < 0 ↔ pivot < 0 then 0 else 1
      if d = 0 then
        upper := Coefficients.one (n+1)
        lower := Coefficients.zero (n+1)
      else
        let raw := Coefficients.remainder (d-1) r.upper r.lower
        let scale := ((pivot⁻¹ : ℝ) : ℂ)
        upper := Coefficients.scale scale r.lower
        lower := Coefficients.scale scale raw
    let axis := axisTotal auxiliary count
    return {
      rows := rows, pivots := pivots, rightRoots := count,
      axisRoots := axis,
      stable := decide (count = 0 ∧ axis = 0) }
end
end RouthHurwitz.ComplexRouth
