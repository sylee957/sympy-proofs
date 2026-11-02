module

public import SympyProofs.Sum.Gosper.Backend.Basic
public import SympyProofs.Sum.Gosper.Backend.Linear
public import SympyProofs.Sum.Gosper.Backend.Normalization

/-! Polynomial normalization and coefficient descent over the input ring. -/

@[expose] public section

namespace Gosper.Algorithm

open Polynomial

/-- Normalize over the input ring `L`, then solve over the chosen constant domain `K`. -/
structure TermBackend (K L : Type*) [CommRing K] [IsDomain K] [CommRing L] [IsDomain L] where
  normalization : NormalizationBackend L
  solver : LinearBackend K
  descend : L → Option K

/-- The coefficient test returns exactly the preimage under the coefficient embedding. -/
def CoefficientDescentValid {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    (descendCoeff : F → Option K) : Prop :=
  ∀ c a, descendCoeff c = some a ↔ algebraMap K F a = c

/-- An exact coefficient converter ensures that the coefficient map is injective. -/
theorem CoefficientDescentValid.injective {K F : Type*} [CommRing K] [CommRing F]
    [Algebra K F] {descendCoeff : F → Option K}
    (hdesc : CoefficientDescentValid descendCoeff) :
    Function.Injective (algebraMap K F) := by
  intro a b h
  apply Option.some.inj
  calc
    some a = descendCoeff (algebraMap K F a) := ((hdesc _ a).mpr rfl).symm
    _ = some b := (hdesc _ b).mpr h.symm

/-- Correctness contracts for normalization, linear solving, and coefficient descent. -/
structure TermBackend.Valid {K L : Type*} [CommRing K] [IsDomain K]
    [CommRing L] [IsDomain L] [Algebra K L] (backend : TermBackend K L) : Prop where
  normalization : backend.normalization.Valid
  solver : backend.solver.Valid
  descend : CoefficientDescentValid backend.descend

/-- Identity conversion satisfies the descent contract over the same coefficient ring. -/
@[simp] theorem coefficientDescentValid_self {R : Type*} [CommRing R] :
    CoefficientDescentValid (some : R → Option R) := by
  intro c a
  simp [Algebra.algebraMap_self, eq_comm]

variable {K : Type*} [Field K]

/-- Use a field backend with identity coefficient conversion. -/
noncomputable def TermBackend.self [CharZero K] [DecidableEq K]
    [DecidablePred (IsLocalization.IsInteger ℤ : K → Prop)]
    (backend : Backend K) : TermBackend K K where
  normalization := backend.toNormalization
  solver := backend.toLinear
  descend := some

theorem TermBackend.self_valid [CharZero K] [DecidableEq K]
    [DecidablePred (IsLocalization.IsInteger ℤ : K → Prop)]
    (backend : Backend K) (hbackend : backend.Valid) :
    (TermBackend.self backend).Valid where
  normalization := backend.toNormalization_valid hbackend
  solver := backend.toLinear_valid hbackend
  descend := coefficientDescentValid_self

end Gosper.Algorithm
