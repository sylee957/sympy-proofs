import SympyProofs.ComplexRouthHurwitz.Exact.Model.Basic

/-! Compressed fraction-free complex Routh table. Loop rows store integers;
their degree parity determines the real or imaginary interpretation. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial Model

abbrev Row (N : ℕ) := Vector ℤ N

def entry {N} (a : Row N) (j : ℕ) : ℤ := if h : j < N then a[j] else 0

def scalar (real : Bool) (x : ℤ) : GaussianInt := if real then ⟨x, 0⟩ else ⟨0, x⟩

def decode {N} (n : ℕ) (a : Row N) : Rows.Row N :=
  Vector.ofFn (fun j => scalar (n%2 == j.val%2) a[j])

def encode {N} (n : ℕ) (a : Rows.Row N) : Row N :=
  Vector.ofFn (fun j => if n%2 = j.val%2 then a[j].re else a[j].im)

/-- Integer numerator, with the sign of the imaginary product determined by parity. -/
def numerator {N} (d : ℕ) (u v : Row N) (j : Fin N) : ℤ :=
  let A := entry u (d+1)
  let B := entry v d
  let g := B * entry u d - A * entry v (d-1)
  B^2*u[j] + (if d%2 = j.val%2 then -g else g)*v[j] -
    A*B*(if j.val = 0 then 0 else entry v (j.val-1))

def nextLower {N} (d : ℕ) (D : ℤ) (u v : Row N) : Row N :=
  let A := entry u (d+1)
  let B := entry v d
  let g := B * entry u d - A * entry v (d-1)
  let square := B^2
  let product := A*B
  Vector.ofFn (fun j => (square*u[j] +
    (if d%2=j.val%2 then -g else g)*v[j] -
    product*(if j.val=0 then 0 else entry v (j.val-1))) / D)

structure Pair (N : ℕ) where
  upper : Row N
  lower : Row N

def scan {N} (a : Rows.Row N) (n : ℕ) : Pair N := {
  upper := Vector.ofFn (fun j => if n%2=j.val%2 then a[j].re else a[j].im)
  lower := Vector.ofFn (fun j => if n%2=j.val%2 then a[j].im else a[j].re) }

def initialRows {N} (a : Rows.Row N) (n : ℕ) : Pair N :=
  let r := scan a n
  let z := Rows.entry a n
  { upper := r.upper
    lower := if z.im=0 then r.lower else Vector.ofFn (fun j =>
      z.re*r.lower[j] + (if n%2=j.val%2 then -z.im else z.im)*r.upper[j]) }

def derivative {N} (u : Row N) : Row N :=
  Vector.ofFn (fun j => entry u (j.val+1) * (j.val+1 : ℕ))

/-- Ordinary and auxiliary steps keep integer coordinates. A reciprocal repair
uses Gaussian coordinates temporarily, then immediately packs its two rows. -/
def repair {N} (d : ℕ) (u v : Row N) : Pair N :=
  if v = Vector.replicate N 0 then { upper := u, lower := derivative u }
  else if entry v d = 0 then
    let upper := decode (d+1) u
    let lower := decode d v
    let offset := Rows.repairOffset d upper lower
    let combined := Rows.add upper lower
    scan (Rows.reciprocal combined (d+1) offset) (d+1)
  else { upper := u, lower := v }

structure Result (N : ℕ) where
  rows : List (Row N)
  pivots : List ℤ
  rightRoots : ℕ
  axisRoots : ℕ
  stable : Bool

/-- The table stores one integer per coordinate. For row pair k, the upper
pattern is n-k and the lower pattern n-k-1. Constants need no table steps. -/
def run (p : GaussianInt[X]) : Result (p.natDegree+1) := Id.run do
  let n := p.natDegree
  let coefficients := Vector.ofFn (fun j : Fin (n+1) => phase p.leadingCoeff * p.coeff j.val)
  if n=0 then
    return { rows := [], pivots := [], rightRoots := 0, axisRoots := 0, stable := true }
  else
    let initial := scan coefficients n
    let mut upper := initial.upper
    let mut lower := initial.lower
    let mut rows := []
    let mut pivots : List ℤ := []
    let mut count := 0
    let mut auxiliary : Option Auxiliary := none
    let leading := coefficients[n]
    let mut divisor : ℤ := 1
    if leading.im ≠ 0 then
      lower := Vector.ofFn (fun j => leading.re*lower[j] +
        (if n%2=j.val%2 then -leading.im else leading.im)*upper[j])
      divisor := leading.re
    for k in List.range n do
      let d := n-(k+1)
      auxiliary := if lower = Vector.replicate (n+1) 0 ∧ auxiliary.isNone then
        some { degree := d+1, rightBefore := count } else auxiliary
      divisor := if entry lower d=0 then 1 else divisor
      let r := repair d upper lower
      rows := rows ++ [r.upper,r.lower]
      let pivot := entry r.lower d
      pivots := pivots ++ [pivot]
      count := count + if entry r.upper (d+1)<0 ↔ pivot<0 then 0 else 1
      if d=0 then
        upper := Vector.ofFn (fun j => if j.val=0 then 1 else 0)
        lower := Vector.replicate (n+1) 0
      else
        upper := r.lower
        lower := nextLower d divisor r.upper r.lower
      divisor := pivot^2
    let axis := axisTotal auxiliary count
    return {
      rows := rows, pivots := pivots, rightRoots := count, axisRoots := axis,
      stable := decide (count=0 ∧ axis=0) }


end RouthHurwitz.ComplexRouth.Exact.Gaussian
