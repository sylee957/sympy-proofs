module

public import SympyProofs.Sum.Gosper.Backend.Rref
public import SympyProofs.Sum.Gosper.Backend.FieldExtension

/-! Operations and contracts for Gosper normalization, descent, and solving. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial IsLocalization

/-- Normalize over `L`, then solve over the chosen constant domain `K`. -/
structure TermBackend (K L : Type*) [CommRing K] [IsDomain K] [CommRing L] [IsDomain L] where
  gcd : L[X] → L[X] → L[X]
  exactDiv : L[X] → L[X] → L[X]
  resultant : L[X][X] → L[X][X] → L[X]
  naturalRoots : L[X] → Finset ℕ
  integerRatio : K → K → Option ℤ
  zeros : (m n : ℕ) → Matrix (Fin m) (Fin n) K
  setElement : {m n : ℕ} → Matrix (Fin m) (Fin n) K →
    Fin m → Fin n → K → Matrix (Fin m) (Fin n) K
  rref : {m n : ℕ} → Matrix (Fin m) (Fin n) K → RrefResult K m n
  descend : L → Option K

/-- Correctness contracts for normalization, solving, and coefficient descent. -/
structure TermBackend.Valid {K R : Type*} [CommRing K] [IsDomain K]
    [CommRing R] [IsDomain R] [Algebra K R] (backend : TermBackend K R) : Prop where
  gcd_dvd_left : ∀ p q, backend.gcd p q ∣ p
  gcd_dvd_right : ∀ p q, backend.gcd p q ∣ q
  gcd_greatest : ∀ (p q d : R[X]), d ∣ p → d ∣ q → d ∣ backend.gcd p q
  exactDiv_mul : ∀ (p d : R[X]), d ≠ 0 → d ∣ p → d * backend.exactDiv p d = p
  resultant_eq : ∀ p q : R[X][X], p ≠ 0 → q ≠ 0 →
    ∃ c : R, c ≠ 0 ∧ backend.resultant p q = C c * Polynomial.resultant p q
  mem_naturalRoots : ∀ p : R[X], p ≠ 0 → ∀ j : ℕ,
    j ∈ backend.naturalRoots p ↔ p.eval (j : R) = 0
  integerRatio_eq_some : ∀ a b, b ≠ 0 → ∀ z : ℤ,
    backend.integerRatio a b = some z ↔ a = (z : K) * b
  zeros_eq : ∀ m n, backend.zeros m n = 0
  setElement_apply : ∀ {m n} (M : Matrix (Fin m) (Fin n) K) i j value i' j',
    backend.setElement M i j value i' j' =
      if i' = i ∧ j' = j then value else M i' j'
  rref_valid : ∀ {m n} (M : Matrix (Fin m) (Fin n) K),
    ((backend.rref M).map (algebraMap K (FractionRing K))).Valid
      (M.map (algebraMap K (FractionRing K)))
  descend : ∀ c a, backend.descend c = some a ↔ algebraMap K R a = c

/-- Exact coefficient descent ensures that the coefficient map is injective. -/
theorem TermBackend.Valid.algebraMap_injective {K R : Type*} [CommRing K] [IsDomain K]
    [CommRing R] [IsDomain R] [Algebra K R] {backend : TermBackend K R}
    (hbackend : backend.Valid) : Function.Injective (algebraMap K R) := by
  intro a b h
  apply Option.some.inj
  calc
    some a = backend.descend (algebraMap K R a) := ((hbackend.descend _ a).mpr rfl).symm
    _ = some b := (hbackend.descend _ b).mpr h.symm

end Gosper.Algorithm
