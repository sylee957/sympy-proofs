module

public import SympyProofs.Calculus.Antiderivative.Program.Decision
public import SympyProofs.Calculus.Antiderivative.Algebra.TangentUnit
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Answer
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Solve
public import SympyProofs.Calculus.Antiderivative.Program.Constants.Parameters

/-! Integration, differential equations, and admissibility on the given tower. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

/-- Decisions on the given field. Multiple queries can share the same recursive level. -/
structure Operations (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    [Div R] (n : ℕ) where
  admissible : Thunk Bool
  integrate : K R n → Result R n
  solve : K R n → List (K R n) → List (K R n) × List (List (K R 0))

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

/-- The integration and equation decisions of a level, together with its admissibility check. -/
def Operations.ofLevel [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]
    (t : Tower R n) (hf : t.TangentFree) : Operations R n :=
  let level := t.level hf
  ⟨⟨fun _ => t.checkSteps hf⟩, level.integrate, level.solve⟩

/-- Transport both decisions through the same change of coordinates. -/
def Operations.inCoordinates (ops : Operations S n) (input : K R n → K S n)
    (answer : Result S n → Result R n)
    (solutions : ℕ → List (K S n) × List (List (K S 0)) → List (K R n) × List (List (K R 0))) :
    Operations R n where
  admissible := ops.admissible
  integrate f := answer (ops.integrate (input f))
  solve f gs := solutions gs.length (ops.solve (input f) (gs.map input))

namespace Trigonometric

/-- Data passed from one polynomial step to the next while visiting native generators.
The velocities differentiate coefficients and the fraction map interprets native inputs. -/
structure Recursion (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [DecidableEq S] [NormalizedGCDMonoid S] [Div S] (n : ℕ) where
  value : K R n → K S n
  velocities : List (K S n)
  level : Level S n
  admissible : Thunk Bool

variable [NatBound (K S 0)] [IntegerRelations (K S 0)] [ConstantFactors (K S 0)]

/-- Extend the coefficient derivative and the polynomial solver by a single generator. -/
def Recursion.step (s : Recursion R S n) (g : ReducedGen (K S n)) (z : K S (n+1)) :
    Recursion R S (n+1) :=
  let D := K.der s.velocities
  let v := match g with
    | .prim b => K.lift b
    | .exp u => K.lift (D u) * K.gen
  ⟨substitute s.value z, s.velocities.map K.lift ++ [v], stepLevel D g s.level,
    ⟨fun _ => s.admissible.get && g.check D s.level⟩⟩

/-- Build the polynomial decisions directly along the native tower. A tangent step uses
the exponential of 2iu and interprets the tangent as a rational function of that generator. -/
def recursion (constants : K R 0 → K S 0) (i : K S 0) : {m : ℕ} → Tower R m → Recursion R S m
  | _, .base => ⟨constants, [], baseLevel S, ⟨fun _ => true⟩⟩
  | _, .step t g =>
    let s := recursion constants i t
    match g with
    | .prim b => s.step (.prim (s.value b)) K.gen
    | .exp u => s.step (.exp (s.value u)) K.gen
    | .tan u => s.step (.exp (2 * K.ofConst i * s.value u)) (Kind.Tan.generator i)

end Trigonometric

open Trigonometric

/-- Run tangent arithmetic over a field containing i and return answers in caller coordinates. -/
def Tower.tangentOperations [NatBound (K S 0)] [IntegerRelations (K S 0)] [ConstantFactors (K S 0)]
    (t : Tower R n) (constants : K R 0 → K S 0) (i : K S 0)
    (answer : Result S n → Result R n)
    (solutions : ℕ → List (K S n) × List (List (K S 0)) → List (K R n) × List (List (K R 0))) :
    Operations R n :=
  let s := recursion constants i t
  let ops : Operations S n := ⟨s.admissible, s.level.integrate, s.level.solve⟩
  ops.inCoordinates s.value answer solutions

/-- Integration, solving and the admissibility test for the original tower. Tangent steps use
an imaginary unit for arithmetic and return their answers over the original constants. -/
def Tower.operations [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]
    [Decidable (IsSquare (-1 : K R 0))] (t : Tower R n) : Operations R n :=
  if hf : t.TangentFree then
    Operations.ofLevel t hf
  else if hs : IsSquare (-1 : K R 0) then
    let i := tangentUnit (K R 0)
    t.tangentOperations id i (t.restoreResult i)
      fun _ (xs, rows) => (xs.map (t.restore i), rows)
  else
    letI : Fact (¬ IsSquare (-1 : K R 0)) := ⟨hs⟩
    let i := K.C (WithI.imaginary (K R 0))
    t.tangentOperations (fun a => K.C (QuadraticAlgebra.C a : WithI (K R 0))) i
      (Descent.result ∘ t.restoreResult i)
      fun width (xs, rows) => Descent.solution width (xs.map (t.restore i), rows)

end SympyProofs.Calculus.Antiderivative
