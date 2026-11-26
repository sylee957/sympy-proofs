module

public import SympyProofs.Calculus.Antiderivative.Program.Decision
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Answer
public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Solve

/-! An exponential tower for proving the native tangent recursion correct. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}

namespace Trigonometric

/-- A reduced tower over the extended constants and the interpretation of an original input. -/
structure Compiled (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (n : ℕ) where
  tower : Tower S n
  value : K R n → K S n
  tangentFree : tower.TangentFree

end Trigonometric

open Trigonometric

/-- Compile an entire mixed tower, applying every earlier coordinate change to later
arguments and to the integrand. The target constant field provides an imaginary unit. -/
def Tower.compile (constants : K R 0 → K S 0) (i : K S 0) : {m : ℕ} → Tower R m → Compiled R S m
  | _, .base => ⟨.base, constants, rfl⟩
  | _, .step t g =>
    let c := t.compile constants i
    match g with
    | .prim b => ⟨c.tower.step (.prim (c.value b)), substitute c.value K.gen, c.tangentFree⟩
    | .exp u => ⟨c.tower.step (.exp (c.value u)), substitute c.value K.gen, c.tangentFree⟩
    | .tan u =>
      ⟨Kind.Tan.tower c.tower i (c.value u), substitute c.value (Kind.Tan.generator i),
        c.tangentFree⟩

/-- Include rational coefficients in the Gaussian rationals when tangent inputs start over ℚ. -/
def Trigonometric.gaussianConstant (c : K ℤ 0) : K Gaussian 0 := K.C (K.toConstants ℚ c : ℚ)

/-- Compile rational input towers using an exact pair of rationals for each extended constant. -/
def Tower.gaussian (t : Tower ℤ n) : Compiled ℤ Gaussian n :=
  t.compile gaussianConstant (K.C Gaussian.I)

/-- Adjoin i to the computable constant field of an arbitrary input tower in which −1 is
a nonsquare. Coefficients and answers use pairs of original field elements. -/
def Tower.adjoinI [Fact (¬ IsSquare (-1 : K R 0))] (t : Tower R n) :
    Compiled R (WithI (K R 0)) n :=
  t.compile (fun a => K.C (QuadraticAlgebra.C a : WithI (K R 0))) (K.C (WithI.imaginary _))

/-- Check the input tower using the specified extension of its coefficient constants. -/
def Tower.admissibleOriginal [NatBound (K S 0)] [IntegerRelations (K S 0)]
    [ConstantFactors (K S 0)] (t : Tower R n) (constants : K R 0 → K S 0) (i : K S 0) : Bool :=
  let c := t.compile constants i
  c.tower.checkSteps c.tangentFree

/-- Check a mixed input tower by adjoining an imaginary unit to its coefficient constants. -/
def Tower.admissibleAdjoinI [Fact (¬ IsSquare (-1 : K R 0))] [NatBound (K R 0)]
    [IntegerRelations (K R 0)] [ConstantFactors (K R 0)] (t : Tower R n) : Bool :=
  t.adjoinI.tower.checkSteps t.adjoinI.tangentFree

section

variable [NatBound (K S 0)] [IntegerRelations (K S 0)] [ConstantFactors (K S 0)]

/-- Check the tower and integrate a rational function expressed in its original coordinates.
The answer uses the coordinates of the compiled tower. -/
def Trigonometric.Compiled.integrate (c : Compiled R S n) (f : K R n) : Option (Result S n) :=
  if c.tower.checkSteps c.tangentFree then
    some ((c.tower.level c.tangentFree).integrate (c.value f))
  else none

/-- Solve the parametric differential equation with all inputs in original coordinates.
The field generators in the result use the coordinates of the compiled tower. -/
def Trigonometric.Compiled.solve (c : Compiled R S n) (f : K R n) (gs : List (K R n)) :
    Option (List (K S n) × List (List (K S 0))) :=
  if c.tower.checkSteps c.tangentFree then
    some ((c.tower.level c.tangentFree).solve (c.value f) (gs.map c.value))
  else none

/-- Integrate in a mixed tower and return its primitive in the original generator coordinates,
using the extended coefficient field for logarithmic constants. -/
def Tower.integrateOriginal (t : Tower R n) (constants : K R 0 → K S 0) (i : K S 0)
    (f : K R n) : Option (Result S n) :=
  ((t.compile constants i).integrate f).map (t.restoreResult i)

/-- Solve the parametric differential equation in the original generator coordinates.
Its homogeneous coefficient rows lie in the same extended constant field. -/
def Tower.solveOriginal (t : Tower R n) (constants : K R 0 → K S 0) (i : K S 0)
    (f : K R n) (gs : List (K R n)) : Option (List (K S n) × List (List (K S 0))) :=
  ((t.compile constants i).solve f gs).map fun (xs, rows) => (xs.map (t.restore i), rows)

end

variable [Fact (¬ IsSquare (-1 : K R 0))]
local notation "E" => WithI (K R 0)
variable [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]

/-- Integrate a tangent tower through its quadratic constant extension and return
all field terms, logarithmic moduli, and logarithmic arguments over its original constants. -/
def Tower.integrateAdjoinI (t : Tower R n) (f : K R n) : Option (Result R n) :=
  (t.integrateOriginal (fun a => K.C (QuadraticAlgebra.C a : E))
    (K.C (WithI.imaginary (K R 0))) f).map Descent.result

/-- Solve through an auxiliary imaginary unit, returning all solution generators and
homogeneous parameter rows in the original tower and coefficient field. -/
def Tower.solveAdjoinI (t : Tower R n) (f : K R n) (gs : List (K R n)) :
    Option (List (K R n) × List (List (K R 0))) :=
  (t.solveOriginal (fun a => K.C (QuadraticAlgebra.C a : E)) (K.C (WithI.imaginary (K R 0)))
    f gs).map (Descent.solution gs.length)

end SympyProofs.Calculus.Antiderivative
