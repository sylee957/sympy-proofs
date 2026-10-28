module

public import Mathlib

/-!
# Supplied polynomial computations

Polynomial arithmetic, coefficients, degree, equality, translation, quotients, and remainders
use Mathlib polynomials. Gcd, derivative, resultant,
and integer-root enumeration are supplied operations with separate correctness contracts.

Integer-root enumeration is an additional assumption beyond gcd and derivative.
It must enumerate all integer roots of every nonzero input polynomial exactly once,
in an array whose order is unrestricted. No factorization of the input denominator
is assumed. The existing Gosper resultant
lemmas are reused only as mathematical proofs; its factorization backend is not
an input to this algorithm.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

variable {K : Type*} [Field K] [DecidableEq K]

open Polynomial

structure Primitives (K : Type*) [Field K] where
  gcd : Polynomial K → Polynomial K → Polynomial K
  derivative : Polynomial K → Polynomial K
  resultant : Polynomial (Polynomial K) → Polynomial (Polynomial K) → Polynomial K
  integerRoots : Polynomial K → Array ℤ

structure Primitives.Valid (ops : Primitives K) : Prop where
  gcd_eq : ∀ p q, ops.gcd p q = GCDMonoid.gcd p q
  derivative_eq : ∀ p, ops.derivative p = p.derivative
  resultant_eq : ∀ p q, ops.resultant p q = Polynomial.resultant p q
  mem_integerRoots : ∀ p, p ≠ 0 → ∀ h : ℤ,
    h ∈ ops.integerRoots p ↔ p.eval (h : K) = 0
  nodup_integerRoots : ∀ p, p ≠ 0 → (ops.integerRoots p).toList.Nodup

def Primitives.squarefreePart (ops : Primitives K) (p : Polynomial K) : Polynomial K :=
  p / ops.gcd p (ops.derivative p)

omit [DecidableEq K] in
/-- Exact division preserves the dividend. No division algorithm is reproved. -/
theorem exact_division (p q : Polynomial K) (hq : q ≠ 0) (hd : p % q = 0) :
    q * (p / q) = p := by
  exact EuclideanDomain.mul_div_cancel' hq (EuclideanDomain.mod_eq_zero.mp hd)

/-- Each side of a gcd refinement can be reconstructed from its two pieces. -/
theorem Primitives.Valid.refinement_reconstruct {ops : Primitives K} (h : ops.Valid)
    (u v : Polynomial K) (hu : u ≠ 0) :
    let g := ops.gcd u v
    g * (u / g) = u ∧ g * (v / g) = v := by
  have hg : GCDMonoid.gcd u v ≠ 0 := fun hz => hu ((gcd_eq_zero_iff u v).mp hz).1
  simp only [h.gcd_eq]
  exact ⟨EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left u v),
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right u v)⟩

/-- Extracting a layer and dividing it out preserves every factor. -/
theorem Primitives.Valid.squarefreeStep_reconstruct {ops : Primitives K} (h : ops.Valid)
    (p : Polynomial K) (hp : p ≠ 0) :
    ops.squarefreePart p ≠ 0 ∧
      ops.squarefreePart p * (p / ops.squarefreePart p) = p := by
  have he : ops.gcd p (ops.derivative p) * ops.squarefreePart p = p :=
    (h.refinement_reconstruct p (ops.derivative p) hp).1
  have hs : ops.squarefreePart p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact hp he.symm
  refine ⟨hs, ?_⟩
  apply EuclideanDomain.mul_div_cancel' hs
  exact ⟨ops.gcd p (ops.derivative p), by rw [mul_comm]; exact he.symm⟩

end Gosper.ShiftlessDecomposition
