module

public import SympyProofs.Sum.Gosper.Backend.Linear
public import SympyProofs.Sum.Gosper.Backend.Resultant
public import SympyProofs.Sum.Gosper.Backend.Factorization

/-! Gosper primitives and coefficient descent over the input ring. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Reference field operations with identity coefficient conversion. -/
noncomputable def referenceTermBackend {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [DecidablePred (IsInteger ℤ : K → Prop)] : TermBackend K K where
  gcd p q := GCDMonoid.gcd p q
  exactDiv p d := p / d
  resultant p q := Polynomial.resultant p q
  naturalRoots p := naturalRootsFromFactors (referenceFactor p).2
  integerRatio := fieldIntegerRatio
  descend := some

/-- A valid field backend supplies a valid combined backend. -/
theorem referenceTermBackend_valid {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [DecidablePred (IsInteger ℤ : K → Prop)] :
    (referenceTermBackend (K := K)).Valid where
  gcd_dvd_left p q := gcd_dvd_left p q
  gcd_dvd_right p q := gcd_dvd_right p q
  gcd_greatest _ _ _ hp hq := dvd_gcd hp hq
  exactDiv_mul p d hd hdp := EuclideanDomain.mul_div_cancel' hd hdp
  resultant_eq p q _ _ := ⟨1, one_ne_zero, by simp [referenceTermBackend]⟩
  mem_naturalRoots p hp := (referenceFactor_valid p hp).mem_naturalRoots

  integerRatio_eq_some := fieldIntegerRatio_eq_some
  descend c a := by simp [referenceTermBackend, Algebra.algebraMap_self, eq_comm]

end Gosper.Algorithm
