module

public import SympyProofs.Gosper.Algorithm.Normalization
public import SympyProofs.Gosper.Algorithm.Degree
public import SympyProofs.Gosper.Algorithm.LinearSolve
public import SympyProofs.Gosper.Algorithm.CoefficientSystem
public import SympyProofs.Gosper.Algorithm.Certificate

/-!
# Gosper's algorithm over a coefficient field

The input is P Q : K[X], the polynomial pair obtained from the forward term
ratio a(n+1)/a(n). This is the boundary after SymPy's
`parallel_poly_from_expr((p, q), n, field=True, extension=True)`.

Control flow is explicit. Arithmetic uses Mathlib polynomials, including gcd,
quotient, translation and resultant. The coefficient equation uses a matrix
over K with explicit Gaussian elimination, analogous to a DomainMatrix solve.
There is no custom dense polynomial representation or arbitrary solver oracle.

This model is noncomputable where Mathlib's polynomial/root operations or
integer recognition are noncomputable. `Algorithm.Correctness` proves summation
soundness, and `Algorithm.Completeness` proves that for nonzero inputs the
procedure succeeds exactly when a hypergeometric antidifference exists.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K]

local instance algorithmDecidableEq : DecidableEq K := Classical.decEq K

/-- Degree selection, matrix solving, and reconstruction using Mathlib `ofFn`.
A negative signed bound skips the matrix solve. -/
def solvePolynomial (A B C : K[X]) : Option K[X] := Id.run do
  let d := degreeBound A B C
  if d < 0 then return none
  let some c := solveLinear (coefficientSystem A B C d.toNat)
      (toFn (equationDegree A B C d.toNat + 1) C) | return none
  return some (ofFn (d.toNat + 1) c)

theorem solvePolynomial_sound (A B C x : K[X])
    (h : solvePolynomial A B C = some x) : A * taylor 1 x - B * x = C := by
  by_cases hd : degreeBound A B C < 0
  · simp [solvePolynomial, hd] at h
  · simp only [solvePolynomial, hd, ↓reduceIte, Id.run, pure] at h
    cases hs : solveLinear (coefficientSystem A B C (degreeBound A B C).toNat)
        (toFn (equationDegree A B C (degreeBound A B C).toNat + 1) C) with
    | none => simp [hs] at h
    | some c =>
      have hx : ofFn ((degreeBound A B C).toNat + 1) c = x := by simpa [hs] using h
      rw [← hx]
      exact (coefficientSystem_correct _ _ _ _ _).mp (solveLinear_sound _ _ _ hs)

structure Certificate (K : Type*) [Field K] where
  numerator : K[X]
  denominator : K[X]

/-- Normalize, solve the bounded polynomial equation, and return B*x/C
without reducing the final fraction.
All polynomial operations below are Mathlib operations over K. The soundness
proof establishes the returned identity without runtime checks. Correctness and
completeness theorems state their nonzero-input assumptions separately. -/
def gosperTerm (P Q : K[X]) : Option (Certificate K) := Id.run do
  let normal := gosperNormal P Q
  let B := taylor (-1) normal.B
  let some x := solvePolynomial normal.A B normal.C | return none
  let U := B * x
  let V := normal.C
  return some ⟨U, V⟩

end Gosper.Algorithm
