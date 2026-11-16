module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic

/-!
# Vectors as pure quaternions

A vector `v : ℝ³` is identified with the pure quaternion `ofVector v = v₀ i + v₁ j + v₂ k`.
This is the embedding through which a quaternion acts on vectors, `v ↦ q v q*`, in the
specifications of `RepresentsRotation.lean` and `RepresentsScaledRotation.lean`.
-/

@[expose] public section

namespace SympyQuaternion

open Quaternion

/-- The pure quaternion `v₀ i + v₁ j + v₂ k` of a vector in `ℝ³`. -/
def ofVector (v : Fin 3 → ℝ) : ℍ[ℝ] :=
  ⟨0, v 0, v 1, v 2⟩

theorem ofVector_injective : Function.Injective ofVector := by
  intro v w h
  funext i
  fin_cases i
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

/-- The squared norm of a pure quaternion is the squared length of the vector. -/
theorem normSq_ofVector (v : Fin 3 → ℝ) :
    normSq (ofVector v) = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [normSq_def']
  simp [ofVector]

theorem ofVector_smul (c : ℝ) (v : Fin 3 → ℝ) : ofVector (c • v) = c • ofVector v := by
  ext <;> simp [ofVector]

end SympyQuaternion
