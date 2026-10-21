module

public import SympyProofs.Gosper.Algorithm.LinearElimination

/-!
# Sound and complete linear solving over the coefficient domain

The matrix and right-hand side have statically checked shapes. Gaussian
elimination removes one column per recursive call; `Linear.eliminate_spec`
proves both reconstruction and inconsistency. Free variables are set to zero.
Correctness follows from the elimination proof, without a runtime check.
-/

@[expose] public section

namespace Gosper.Algorithm

variable {K : Type*} [Field K] [DecidableEq K] {m n : ℕ}

def eliminate (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Option (Fin n → K) :=
  Linear.eliminate n A b

def solveLinear (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    Option (Fin n → K) :=
  eliminate A b

theorem solveLinear_eq (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    solveLinear A b = eliminate A b := rfl

theorem solveLinear_sound (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (c : Fin n → K) (h : solveLinear A b = some c) : A.mulVec c = b := by
  exact Linear.eliminate_some A b c h

theorem solveLinear_none_iff (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    solveLinear A b = none ↔ ¬∃ c, A.mulVec c = b := by
  exact Linear.eliminate_none_iff A b

theorem solveLinear_complete (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (∃ c, solveLinear A b = some c) ↔ ∃ c, A.mulVec c = b := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, solveLinear_sound A b c hc⟩
  · intro h
    cases he : eliminate A b with
    | none => exact ((Linear.eliminate_none_iff A b).mp he h).elim
    | some c => exact ⟨c, by rw [solveLinear_eq, he]⟩

end Gosper.Algorithm
