module

public import Mathlib

/-!
# Polynomial operations over the coefficient field

The algorithm uses `Polynomial K` directly. Addition, multiplication, quotient,
remainder, gcd, translation, and resultant correspond to the operations exposed
by SymPy's polynomial layer (`dup_*` / `dmp_*` below its public API). Their dense
or sparse representation is not part of the Gosper model.

Mathlib's polynomial division and root extraction are noncomputable. Membership
in the image of ℤ or ℕ also requires a domain-specific algorithm for execution
over a concrete field. We use their mathematical definitions here, rather than
assuming an oracle for normalization or polynomial equation solving.
-/

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial

variable {K : Type*} [Field K]

local instance polynomialDecidableEq : DecidableEq K := Classical.decEq K

def monic (p : K[X]) : K[X] := C p.leadingCoeff⁻¹ * p

/-- Recognition of an integer in the coefficient field, including negative
integers. A concrete CAS domain supplies an effective version of this test. -/
def integerValue (a : K) : Option ℤ := by
  classical
  exact if h : ∃ n : ℤ, (n : K) = a then some (Classical.choose h) else none

def naturalValue (a : K) : Option ℕ := by
  classical
  exact if h : ∃ n : ℕ, (n : K) = a then some (Classical.choose h) else none

theorem integerValue_eq_some [CharZero K] (a : K) (n : ℤ) :
    integerValue a = some n ↔ (n : K) = a := by
  unfold integerValue
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun he => he ▸ Classical.choose_spec h,
      fun hn => Int.cast_injective ((Classical.choose_spec h).trans hn.symm)⟩
  · simp only [false_iff]
    exact fun hn => h ⟨n, hn⟩

@[simp] theorem integerValue_intCast [CharZero K] (n : ℤ) :
    integerValue (n : K) = some n := (integerValue_eq_some _ _).mpr rfl

theorem naturalValue_eq_some [CharZero K] (a : K) (n : ℕ) :
    naturalValue a = some n ↔ (n : K) = a := by
  unfold naturalValue
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun he => he ▸ Classical.choose_spec h,
      fun hn => Nat.cast_injective ((Classical.choose_spec h).trans hn.symm)⟩
  · simp only [false_iff]
    exact fun hn => h ⟨n, hn⟩

end Gosper.Algorithm
