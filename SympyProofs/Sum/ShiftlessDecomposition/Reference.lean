module

public import SympyProofs.Sum.ShiftlessDecomposition.Primitives
public import SympyProofs.Sum.Gosper.Backend.Resultant

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

/-- Reference shift enumeration via the shift resultant. -/
def resultantShifts (p q : Polynomial K) : Array ℤ :=
  referenceIntegerRoots (Gosper.Algorithm.sylvesterShiftResultant p q)

theorem mem_resultantShifts (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) (h : ℤ) :
    h ∈ resultantShifts p q ↔ ¬IsCoprime p (taylor (h : K) q) := by
  rw [resultantShifts, mem_referenceIntegerRoots _
    (Gosper.Algorithm.sylvesterShiftResultant_ne_zero p q hp hq),
    Gosper.Algorithm.sylvesterShiftResultant_eval]
  simpa [hp] using (Polynomial.resultant_eq_zero_iff (f := p) (g := taylor (h : K) q))

def referencePrimitives : Primitives K where
  gcd := GCDMonoid.gcd
  derivative := Polynomial.derivative
  shifts := resultantShifts

theorem referencePrimitives_valid : (referencePrimitives (K := K)).Valid where
  gcd_eq _ _ := rfl
  derivative_eq _ := rfl
  mem_shifts p q hp hq _ _ := mem_resultantShifts p q hp.ne_zero hq.ne_zero
  nodup_shifts _ _ _ _ _ _ := Finset.nodup_toList _

end Gosper.ShiftlessDecomposition
