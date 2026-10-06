import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Wronskian
import SympyProofs.ComplexRouthHurwitz.Reference.Basic
import SympyProofs.ComplexRouthHurwitz.Table.Reduction

/-! Polynomial specifications used only in correctness proofs. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

/-- A real, strictly positive leading coefficient; monicity is unnecessary. -/
def PositiveLeading (p : ℂ[X]) : Prop :=
  p.leadingCoeff.im = 0 ∧ 0 < p.leadingCoeff.re

/-- The two initial rows produced together by a coefficient scan. -/
structure InitialRows where
  upper : Polynomial ℂ
  lower : Polynomial ℂ

/-- Proof-only reflection formula for the upper initial row. -/
noncomputable def upperPart (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  C (1/2 : ℂ) * (p + C ((-1)^n)*axisReflect p)
/-- Proof-only reflection formula for the lower initial row. -/
noncomputable def lowerPart (p : ℂ[X]) (n : ℕ) : ℂ[X] :=
  C (1/2 : ℂ) * (p - C ((-1)^n)*axisReflect p)

/-- Algebraic specification of the initial pair; the runner uses `Coefficients.scan`. -/
def scan (p : Polynomial ℂ) (n : ℕ) : InitialRows :=
  { upper := upperPart p n, lower := lowerPart p n }

noncomputable def ratio (d : ℕ) (u v : ℂ[X]) : ℝ :=
  (u.coeff (d+2)).re / (v.coeff (d+1)).re
noncomputable def correction (d : ℕ) (u v : ℂ[X]) : ℂ :=
  (u.coeff (d+1) - (ratio d u v : ℂ) * v.coeff d) / v.coeff (d+1)
noncomputable def remainder (d : ℕ) (u v : ℂ[X]) : ℂ[X] :=
  u - C (correction d u v)*v - C (ratio d u v : ℂ)*X*v

/-- Search a finite set of imaginary-axis shifts. For a nonzero deficient
row the Wronskian theorem guarantees a successful candidate. -/
def repairOffset (d : ℕ) (u v : ℂ[X]) : ℕ :=
  let w := wronskian u v
  ((List.range (2*(d+1)+1)).find? (fun j : ℕ => decide (w.eval ((j:ℂ)*Complex.I) ≠ 0))).getD 0

/-- Translate along the imaginary axis, reverse, and normalize the leading coefficient. -/
def reciprocal (p : ℂ[X]) (t : ℝ) : ℂ[X] :=
  let r := (taylor (t*Complex.I) p).reverse
  r * C (conj r.leadingCoeff)

/-- Zero rows use the derivative. A deficient nonzero row uses a finite
imaginary-shift search and reciprocal reversal. Regular pairs are unchanged. -/
def repair (d : ℕ) (u v : ℂ[X]) : InitialRows :=
  if v = 0 then { upper := u, lower := u.derivative }
  else if (v.coeff d).re = 0 then
    scan (reciprocal (u+v) (repairOffset d u v)) (d+1)
  else { upper := u, lower := v }

end
end RouthHurwitz.ComplexRouth
