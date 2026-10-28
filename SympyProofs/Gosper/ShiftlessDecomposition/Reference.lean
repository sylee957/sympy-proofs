module

public import SympyProofs.Gosper.ShiftlessDecomposition.Primitives

/-!
# A reference realization of the primitive contracts

Mathlib supplies a noncomputable reference instance. This witnesses that the
contracts are satisfiable; an implementation can substitute its own routines.
Integer roots are the preimage of the polynomial's roots under the injective
map `ℤ → K`. This reference construction does not require a root-finding algorithm.
-/

@[expose] public section
noncomputable section

namespace Gosper.ShiftlessDecomposition

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def referenceIntegerRoots (p : Polynomial K) : Array ℤ :=
  (p.roots.toFinset.preimage (fun h : ℤ => (h : K)) Int.cast_injective.injOn).toList.toArray

theorem mem_referenceIntegerRoots (p : Polynomial K) (hp : p ≠ 0) (h : ℤ) :
    h ∈ referenceIntegerRoots p ↔ p.eval (h : K) = 0 := by
  simp only [referenceIntegerRoots, List.mem_toArray, Finset.mem_toList, Finset.mem_preimage,
    Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

def referencePrimitives : Primitives K where
  gcd := GCDMonoid.gcd
  derivative := Polynomial.derivative
  resultant := fun p q => Polynomial.resultant p q
  integerRoots := referenceIntegerRoots

theorem referencePrimitives_valid : (referencePrimitives (K := K)).Valid where
  gcd_eq _ _ := rfl
  derivative_eq _ := rfl
  resultant_eq _ _ := rfl
  mem_integerRoots := mem_referenceIntegerRoots
  nodup_integerRoots _ _ := Finset.nodup_toList _

end Gosper.ShiftlessDecomposition
