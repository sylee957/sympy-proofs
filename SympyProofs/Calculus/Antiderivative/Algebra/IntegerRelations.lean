module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants

/-! Effective rational-linear equations on constants. Restricting the kernel to integer
vectors gives all integral relations, including relations involving rational denominators. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Rational rows whose common kernel gives the rational dependencies of a list of constants. -/
class IntegerRelations (Γ : Type) where
  /-- Equations on the coefficients of a rational linear combination that vanishes. -/
  rows : List Γ → List (List ℚ)

/-- Among rational constants there is exactly the input equation. -/
instance : IntegerRelations ℚ := ⟨fun xs => [xs]⟩

/-- Compute rational dependencies after embedding the input constants into another field. -/
@[instance_reducible] def IntegerRelations.ofMap {F G : Type} [IntegerRelations G]
    (f : F → G) : IntegerRelations F :=
  ⟨fun xs => IntegerRelations.rows (xs.map f)⟩

/-- Integer relations on fractions of integers are computed over the rationals. -/
instance : IntegerRelations (K ℤ 0) := IntegerRelations.ofMap (K.toConstants ℚ)

/-- Fractions over a field inherit that field's rational-dependency algorithm. -/
instance {F : Type} [Field F] [IntegerRelations F] : IntegerRelations (K F 0) :=
  IntegerRelations.ofMap (K.toConstants F)

end SympyProofs.Calculus.Antiderivative
