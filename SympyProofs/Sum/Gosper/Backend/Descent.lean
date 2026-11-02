module

public import SympyProofs.Sum.Gosper.Backend.Basic

/-! Backend operations and coefficient descent for solving over a smaller field. -/

@[expose] public section

namespace Gosper.Algorithm

/-- Operations for normalization over `L` and linear solving over `K`, together
with a coefficient conversion to the chosen smaller field. -/
structure TermBackend (K L : Type*) [Field K] [Field L] where
  normalization : Backend L
  solver : Backend K
  descend : L → Option K

variable {K L : Type*} [Field K] [Field L]

/-- The coefficient test returns exactly the preimage under the field embedding. -/
def CoefficientDescentValid [Algebra K L] (descendCoeff : L → Option K) : Prop :=
  ∀ c a, descendCoeff c = some a ↔ algebraMap K L a = c

/-- Identity conversion satisfies the descent contract over the same field. -/
@[simp] theorem coefficientDescentValid_self :
    CoefficientDescentValid (some : K → Option K) := by
  intro c a
  simp [Algebra.algebraMap_self, eq_comm]

/-- The normalization and solver contracts, together with exact coefficient descent. -/
structure TermBackend.Valid [Algebra K L] (backend : TermBackend K L) : Prop where
  normalization : backend.normalization.Valid
  solver : backend.solver.Valid
  descend : CoefficientDescentValid backend.descend

/-- Reuse a backend over one field with identity coefficient conversion. -/
def TermBackend.self (backend : Backend K) : TermBackend K K where
  normalization := backend
  solver := backend
  descend := some

theorem TermBackend.self_valid (backend : Backend K) (hbackend : backend.Valid) :
    (TermBackend.self backend).Valid where
  normalization := hbackend
  solver := hbackend
  descend := coefficientDescentValid_self

end Gosper.Algorithm
