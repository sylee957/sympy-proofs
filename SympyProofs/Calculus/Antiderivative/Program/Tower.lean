module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Heights
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Derivation

/-! Differential towers in primitive, exponential and tangent coordinates. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- A generator over the field of the preceding tower. -/
inductive Gen (F : Type)
  /-- A generator with the given derivative. -/
  | prim (b : F)
  /-- The exponential of an element of the lower field. -/
  | exp (u : F)
  /-- The tangent of an element of the lower field. -/
  | tan (u : F)

/-- A tower of rational function fields with the indicated number of generators. -/
inductive Tower (R : Type) [CommRing R] [IsDomain R] : ℕ → Type
  /-- Start with the coefficient field. -/
  | base : Tower R 0
  /-- Extend the tower with a generator over its current field. -/
  | step {n} (t : Tower R n) (g : Gen (K R n)) : Tower R (n+1)

/-- The two possible steps of the polynomial recursion after tangent substitution. -/
inductive ReducedGen (F : Type)
  | prim (b : F)
  | exp (u : F)

/-- Interpret a step of the polynomial recursion as an ordinary tower generator. -/
@[coe] def ReducedGen.toGen {F : Type} : ReducedGen F → Gen F
  | .prim b => .prim b
  | .exp u => .exp u

instance {F : Type} : Coe (ReducedGen F) (Gen F) := ⟨ReducedGen.toGen⟩

namespace Tower

variable {R : Type} [CommRing R] [IsDomain R]

/-- Check whether any generator requires the tangent substitution. -/
def hasTangent : {n : ℕ} → Tower R n → Bool
  | _, .base => false
  | _, .step t (.prim _) => t.hasTangent
  | _, .step t (.exp _) => t.hasTangent
  | _, .step _ (.tan _) => true

/-- The ordinary tower is in coordinates accepted by the polynomial recursion. -/
abbrev TangentFree {n : ℕ} (t : Tower R n) : Prop := t.hasTangent = false

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R]

/-- Generator derivatives in index order, expressed in the field of the whole tower. -/
def gens : {n : ℕ} → Tower R n → List (K R n)
  | _, .base => []
  | _, .step t g =>
    let v := t.gens
    let d := match g with
      | .prim b => K.lift b
      | .exp u => K.lift (K.der v u) * K.gen
      | .tan u => K.lift (K.der v u) * (1 + K.gen ^ 2)
    v.map K.lift ++ [d]

/-- Differentiate a field element using the native velocities. -/
def D {n : ℕ} (t : Tower R n) : K R n → K R n := K.der t.gens

end Tower

end SympyProofs.Calculus.Antiderivative
