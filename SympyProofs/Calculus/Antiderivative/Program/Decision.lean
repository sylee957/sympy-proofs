module

public import SympyProofs.Calculus.Antiderivative.Program.Elementary
public import SympyProofs.Calculus.Antiderivative.Program.LogRelations
public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Tower

/-! The simultaneous recursion for elementary integration, differential equations and
rational logarithmic relations, with certified univariate factorization in the tower fields. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)]

/-- All four level operations at a new generator, using the level already computed below. -/
def stepLevel {n : ℕ} (D : K R n → K R n)
    (g : ReducedGen (K R n)) (lower : Level R n) : Level R (n + 1) where
  integrate := Elementary.integrate D g lower
  elementaryBasis := Elementary.basis D g lower
  solve := Solve.step D g lower
  logRelations ws :=
    let data := logPoleData g ws
    factoredLogStep D g lower.logRelations data (factorTower data.normalDen)

/-- Build the level after all tangent steps have been put in exponential coordinates. -/
def Tower.level : {n : ℕ} → (t : Tower R n) → t.TangentFree → Level R n
  | _, .base, _ => baseLevel R
  | _, .step t (.prim b), hf => stepLevel t.D (.prim b) (t.level hf)
  | _, .step t (.exp u), hf => stepLevel t.D (.exp u) (t.level hf)
  | _, .step _ (.tan _), hf => nomatch hf

omit [NatBound (K R 0)] [IntegerRelations (K R 0)] [ConstantFactors (K R 0)] in
/-- Decide whether a single new generator keeps the same constants. -/
def ReducedGen.check {n : ℕ} (D : K R n → K R n) (lower : Level R n) (g : ReducedGen (K R n)) :
    Bool :=
  match g with
  | .prim b => (lower.rde 0 b).isNone
  | .exp u => lower.expOk D u

/-- Check each extension using the differential decisions of the preceding tower. -/
def Tower.checkSteps : {n : ℕ} → (t : Tower R n) → t.TangentFree → Bool
  | _, .base, _ => true
  | _, .step t (.prim b), hf => t.checkSteps hf && (ReducedGen.prim b).check t.D (t.level hf)
  | _, .step t (.exp u), hf => t.checkSteps hf && (ReducedGen.exp u).check t.D (t.level hf)
  | _, .step _ (.tan _), hf => nomatch hf

end SympyProofs.Calculus.Antiderivative
