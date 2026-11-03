module

public import SympyProofs.Sum.Gosper.Backend.Linear
public import SympyProofs.Sum.Gosper.Backend.Resultant
public import SympyProofs.Sum.Gosper.Backend.Factorization

/-! Gosper primitives and coefficient descent over the input ring. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Reference field operations with identity coefficient conversion and supplied RREF. -/
noncomputable def referenceTermBackend {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)] (rref : RrefOperation K) : TermBackend K K where
  gcd p q := GCDMonoid.gcd p q
  exactDiv p d := p / d
  resultant p q := Polynomial.resultant p q
  naturalRoots p := naturalRootsFromFactors (referenceFactor p).2
  integerRatio := fieldIntegerRatio
  zeros _ _ := 0
  setElement M i j value := Function.update M i (Function.update (M i) j value)
  rref := rref
  descend := some

/-- A valid field backend supplies a valid combined backend. -/
theorem referenceTermBackend_valid {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [DecidablePred (IsInteger ℤ : K → Prop)] (rref : RrefOperation K)
    (hrref : ∀ {m n} (M : Matrix (Fin m) (Fin n) K), (rref M).Valid M) :
    (referenceTermBackend rref).Valid where
  gcd_dvd_left p q := gcd_dvd_left p q
  gcd_dvd_right p q := gcd_dvd_right p q
  gcd_greatest _ _ _ hp hq := dvd_gcd hp hq
  exactDiv_mul p d hd hdp := EuclideanDomain.mul_div_cancel' hd hdp
  resultant_eq p q _ _ := ⟨1, one_ne_zero, by simp [referenceTermBackend]⟩
  mem_naturalRoots p hp := (referenceFactor_valid p hp).mem_naturalRoots

  integerRatio_eq_some := fieldIntegerRatio_eq_some
  zeros_eq _ _ := rfl
  setElement_apply M i j value i' j' := by
    by_cases hi : i' = i <;> by_cases hj : j' = j <;>
      simp [referenceTermBackend, Function.update, hi, hj]
  rref_valid := rref_valid_fractionRing rref hrref
  descend c a := by simp [referenceTermBackend, Algebra.algebraMap_self, eq_comm]

end Gosper.Algorithm
