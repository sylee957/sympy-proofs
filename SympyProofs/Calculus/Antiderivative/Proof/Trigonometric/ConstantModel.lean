module

public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Ground
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Extending a model embedding to the computable quadratic constant field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

/-- Interpret a real-imaginary pair by choosing the square root of negative one in the
model. Its real and imaginary coefficients use the original constant embedding. -/
noncomputable def quadraticModelHom (j : k) (hj : j^2 = -1) : WithI (K R 0) →+* k := by
  letI := (Model.constantHom (R := R) k).toAlgebra
  exact (QuadraticAlgebra.lift ⟨j,by simpa [pow_two] using hj⟩).toRingHom

@[simp] theorem quadraticModelHom_C (j : k) (hj : j^2 = -1) (a : K R 0) :
    quadraticModelHom k j hj (QuadraticAlgebra.C a) = Model.constantHom k a := by
  change Model.constantHom k a * 1 + Model.constantHom k 0 * j = _
  simp

@[simp] theorem quadraticModelHom_imaginary (j : k) (hj : j^2 = -1) :
    quadraticModelHom k j hj (WithI.imaginary (K R 0)) = j := by
  change Model.constantHom (R := R) k 0 * 1 + Model.constantHom (R := R) k 1 * j = _
  simp

/-- Every algebraically closed model supports the quadratic extension, with the image of
the imaginary unit satisfying its defining equation. -/
theorem exists_quadraticModelHom [IsAlgClosed k] :
    ∃ (h : WithI (K R 0) →+* k), (∀ a, h (QuadraticAlgebra.C a) = Model.constantHom k a) ∧
      h (WithI.imaginary (K R 0)) ^ 2 = -1 := by
  obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) zero_lt_two
  exact ⟨quadraticModelHom k j hj,quadraticModelHom_C k j hj,by simpa using hj⟩

theorem modelConstant_C (a : R) :
    Model.constantHom k (K.C a : K R 0) = algebraMap R k a := by
  apply (Model.C k 0).injective
  rw [Model.C_zero_constantHom]
  simp [val, Model.C]

variable [Fact (¬ IsSquare (-1 : K R 0))]

/-- With the chosen extension of the model, the ground embedding used by the executable
compiler satisfies the compatibility hypothesis of the transfer theorems. -/
theorem quadraticConstantHom_compatible (j : k) (hj : j^2 = -1) (a : K R 0) :
    letI := (quadraticModelHom (R := R) k j hj).toAlgebra
    Model.constantHom k (quadraticConstantHom a) = Model.constantHom k a := by
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  change Model.constantHom k (quadraticConstantHom a) = Model.constantHom k a
  rw [quadraticConstantHom_apply, modelConstant_C]
  exact quadraticModelHom_C k j hj a

/-- In the compatible model the compiler's adjoined unit has precisely the chosen value. -/
theorem quadraticI_value (j : k) (hj : j^2 = -1) :
    letI := (quadraticModelHom (R := R) k j hj).toAlgebra
    Model.constantHom k (K.C (WithI.imaginary (K R 0)) : K (WithI (K R 0)) 0) = j := by
  let _ := (quadraticModelHom (R := R) k j hj).toAlgebra
  change Model.constantHom k (K.C (WithI.imaginary (K R 0)) : K (WithI (K R 0)) 0) = j
  rw [modelConstant_C]
  exact quadraticModelHom_imaginary k j hj

end SympyProofs.Calculus.Antiderivative.Trigonometric
