import SympyProofs.ComplexRouthHurwitz.Exact.GaussianInt
import SympyProofs.ComplexRouthHurwitz.Reference.Basic

/-! Gaussian row operations used by reciprocal repair and by the arithmetic
proof model. The executable integer-row runner is in `Exact.Basic`. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian.Model
open Polynomial

namespace Rows
abbrev Row (N : ℕ) := Vector GaussianInt N

/-- Zero extension is used only for shifted coefficient indices. -/
def entry {N : ℕ} (a : Row N) (j : ℕ) : GaussianInt := if h : j < N then a[j] else 0

def zero (N : ℕ) : Row N := Vector.ofFn (fun _ => 0)
def one (N : ℕ) : Row N := Vector.ofFn (fun j => if j.val = 0 then 1 else 0)
def add {N : ℕ} (a b : Row N) : Row N := Vector.ofFn (fun j => a[j]+b[j])
def derivative {N : ℕ} (a : Row N) : Row N :=
  Vector.ofFn (fun j => entry a (j.val+1) * (j.val+1 : ℕ))
def eval {N : ℕ} (a : Row N) (z : GaussianInt) : GaussianInt := ∑ j : Fin N, a[j]*z^j.val

structure Pair (N : ℕ) where
  upper : Row N
  lower : Row N

/-- Split each coefficient into its alternating real and imaginary parts. -/
def scan {N : ℕ} (a : Row N) (n : ℕ) : Pair N := {
  upper := Vector.ofFn (fun j => if n%2 = j.val%2 then (a[j].re : GaussianInt) else a[j].im*(⟨0,1⟩ : GaussianInt))
  lower := Vector.ofFn (fun j => if n%2 = j.val%2 then a[j].im*(⟨0,1⟩ : GaussianInt) else (a[j].re : GaussianInt)) }

/-- At most 2(d+1)+1 distinct points suffice for the nonzero Wronskian. -/
def repairOffset {N : ℕ} (d : ℕ) (u v : Row N) : ℕ :=
  let du := derivative u
  let dv := derivative v
  ((List.range (2*(d+1)+1)).find? (fun j : ℕ =>
    let z := (j : GaussianInt)*(⟨0,1⟩ : GaussianInt)
    decide (eval u z * eval dv z - eval du z * eval v z ≠ 0))).getD 0

/-- Shift, reverse at the current degree, and normalize. The binomial sum is
computed directly from coefficients; the repair proof guarantees a nonzero normalization factor. -/
def reciprocal {N : ℕ} (a : Row N) (m : ℕ) (t : ℤ) : Row N :=
  let z := (t : GaussianInt)*(⟨0,1⟩ : GaussianInt)
  let factor := star (eval a z)
  Vector.ofFn (fun i => if i.val ≤ m then
    (∑ j : Fin N, a[j] * (j.val.choose (m-i.val) : GaussianInt) * z^(j.val-(m-i.val))) * factor
    else 0)

def repair {N : ℕ} (d : ℕ) (u v : Row N) : Pair N :=
  if v = zero N then { upper := u, lower := derivative u }
  else if (entry v d).re = 0 then
    scan (reciprocal (add u v) (d+1) (repairOffset d u v)) (d+1)
  else { upper := u, lower := v }
end Rows


/-- A Gaussian unit makes the leading real part positive without coefficient growth. -/
def phase (z : GaussianInt) : GaussianInt :=
  if z.re = 0 then (if z.im < 0 then (⟨0,1⟩ : GaussianInt) else -(⟨0,1⟩ : GaussianInt))
  else if z.re < 0 then -1 else 1

/-- The degree-zero first elimination; a real leading coefficient needs only a scan. -/
def initialRows {N} (a : Rows.Row N) (n : ℕ) : Rows.Pair N :=
  let r := Rows.scan a n
  let z := Rows.entry a n
  { upper := r.upper, lower := if z.im = 0 then r.lower else
      Vector.ofFn (fun j => (z.re : GaussianInt)*r.lower[j] - (z.im : GaussianInt)*(⟨0,1⟩ : GaussianInt)*r.upper[j]) }

def initialDivisor {N} (a : Rows.Row N) (n : ℕ) : ℤ :=
  let z := Rows.entry a n
  if z.im = 0 then 1 else z.re

/-- Coordinatewise pseudo-remainder divided exactly by the stored divisor. -/
def nextLower {N : ℕ} (d : ℕ) (D : ℤ) (u v : Rows.Row N) : Rows.Row N :=
  let A := (Rows.entry u (d+1)).re
  let B := (Rows.entry v d).re
  let γ := (B:GaussianInt)*Rows.entry u d - (A:GaussianInt)*Rows.entry v (d-1)
  Vector.ofFn (fun j => ((B:GaussianInt)^2*u[j] - γ*v[j] - (A:GaussianInt)*(B:GaussianInt)*
      (if j.val = 0 then 0 else Rows.entry v (j.val-1))) / (D:GaussianInt))

end RouthHurwitz.ComplexRouth.Exact.Gaussian.Model
