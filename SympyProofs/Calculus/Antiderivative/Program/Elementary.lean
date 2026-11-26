module

public import SympyProofs.Calculus.Antiderivative.Program.Solve
public import SympyProofs.Calculus.Antiderivative.Program.Step.ParametricResidues
public import SympyProofs.Calculus.Antiderivative.Program.Kind.Prim
public import SympyProofs.Calculus.Antiderivative.Program.Kind.Exp

/-! Elementary integration of constant-linear combinations at a primitive or exponential step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- Add two elementary primitives. -/
def Answer.add (a b : Answer R n) : Answer R n := ⟨a.field + b.field, a.sums ++ b.sums⟩

/-- Combine primitives with constant coefficients. -/
def Answer.combine (cs : List (K R 0)) (as : List (Answer R n)) : Answer R n :=
  (cs.zipWith (fun c a => a.scale c) as).foldl Answer.add ⟨0, []⟩

namespace Elementary

/-- The order at the special pole of the newest generator. -/
def poleOrder (g : ReducedGen (K R n)) (den : Poly (K R n)) : ℕ :=
  match g with
  | .prim _ => 0
  | .exp _ => (den.coeffs.takeWhile (· == 0)).length

/-- The Hermite decomposition of an input column with a shared denominator. -/
structure Parts (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    [Div R] (n : ℕ) where
  /-- Primitive of the exact terms extracted by Hermite reduction. -/
  exactPart : K R (n + 1)
  /-- Numerator of the Laurent polynomial over the designated power of the special pole. -/
  laurent : Poly (K R n)
  /-- Numerator of the remaining proper fraction. -/
  proper : Poly (K R n)
  /-- Squarefree normal denominator, shared by all input columns. -/
  normalDen : Poly (K R n)

/-- Isolate the special pole and remove repeated normal poles. -/
def parts (D : K R n → K R n) (dx den : Poly (K R n)) (k : ℕ) (a : Poly (K R n)) : Parts R n :=
  let separated := Step.separatePole a den k
  let red := Step.hermite D dx separated.normalNum separated.normalDen
  ⟨(red.exactTerms.map (fun (p, q) => K.join p q)).sum,
    (red.numerator / red.denominator) * Poly.X ^ k + separated.specialNum,
    red.numerator % red.denominator, red.denominator⟩

/-- Compute derivatives of the residues in the separable algebra defined by the denominator.
An algebraic root of the denominator has velocity given by implicit differentiation. -/
def residueRows (D : K R n → K R n) (dx s : Poly (K R n)) (as : List (Poly (K R n))) :
    List (List (K R 0)) :=
  if s.natDegree = 0 then [] else
    (coefficientSlices (Step.residueDerivatives D dx s as)).flatMap rowsOf

/-- Solve all nonconstant Laurent coefficient equations. The zeroth Laurent coefficient is
reserved for elementary integration below. For a primitive generator one extra leading
unknown accounts for primitives whose degree exceeds that of the input. -/
def coefficients (D : K R n → K R n) (lower : Level R n) (dx : Poly (K R n)) (width k : ℕ) :
    ℕ → List (Solve.Column R n) → List (Solve.Column R n)
  | 0, cols => cols
  | j + 1, cols =>
    if j = k then coefficients D lower dx width k j cols else
      let twist := dx.coeff 1
      let next := Solve.extendSolutions D dx 1 (Poly.C (-(k : K R n) * twist)) lower
        width j cols (((j : K R n) - k) * twist) (cols.map fun v => v.residual.coeff j)
      coefficients D lower dx width k j next

/-- Integrate the subspace of Laurent polynomial combinations admitting elementary integrals. -/
def polynomialBasis (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (k : ℕ) (ps : List (Poly (K R n))) : List (List (K R 0) × Answer R (n + 1)) :=
  let width := ps.length
  let size := (ps.map (·.coeffs.length)).max?.getD 0
  let bound := match g with | .prim _ => size + 1 | .exp _ => size
  let start := Solve.initial ps
  let cols := coefficients D lower (g.velocity D) width k bound start
  (lower.elementaryBasis (cols.map fun v => v.residual.coeff k)).map fun (q, ans) =>
    let v := Solve.combine width cols q
    (v.params, ans.lift.addField (K.join v.solution (Poly.X ^ k)))

/-- An integrable residue direction, with its remaining Laurent polynomial. -/
structure Direction (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    [Div R] (n : ℕ) where
  /-- The coordinates of the direction in the original inputs. -/
  coords : List (K R 0)
  /-- The primitive accumulated from Hermite reduction and the constant residues. -/
  answer : Answer R (n + 1)
  /-- The residual Laurent numerator. -/
  rest : Poly (K R n)

/-- Construct a primitive for the residue part of a direction satisfying the residue equations. -/
def direction (D : K R n → K R n) (dx s : Poly (K R n)) (k : ℕ)
    (ps : List (Parts R n)) (v : List (K R 0)) : Option (Direction R n) := do
  let p := Solve.mix v (ps.map Parts.proper)
  let (logs, corr) ← Residue.logPart p s (Step.polyDer D dx s) (dx.coeff 1)
  let exactPart := Level.combine v (ps.map Parts.exactPart)
  return ⟨v, ⟨exactPart, logs⟩, Solve.mix v (ps.map Parts.laurent) + Poly.monomial k corr⟩

/-- Compute the Laurent shift and the directions passing the normal-residue equations. -/
def directions (D : K R n → K R n) (g : ReducedGen (K R n)) (gs : List (K R (n + 1))) :
    ℕ × List (Direction R n) :=
  let (as, den) := commonDen gs
  let dx := g.velocity D
  let k := poleOrder g den
  let ps := as.map (parts D dx den k)
  let s := (ps.head?.map Parts.normalDen).getD 1
  let rows := residueRows D dx s (ps.map Parts.proper)
  (k, (Linear.kernel rows gs.length).filterMap (direction D dx s k ps))

/-- Integrate the Laurent remainders and express the result in original coordinates. -/
def fromDirections (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n) (width k : ℕ)
    (dirs : List (Direction R n)) : List (List (K R 0) × Answer R (n + 1)) :=
  (polynomialBasis D g lower k (dirs.map Direction.rest)).map fun (q, a) =>
    (Solve.coordinates width q (dirs.map Direction.coords),
      a.add (Answer.combine q (dirs.map Direction.answer)))

/-- Compute generating directions and regular primitives for elementary combinations. -/
def basis (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (gs : List (K R (n + 1))) :
    List (List (K R 0) × Answer R (n + 1)) :=
  let (s, dirs) := directions D g gs
  fromDirections D g lower gs.length s dirs

/-- Decide elementary integration of one input without constructing a parametric basis. -/
def integrate (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n) (x : K R (n + 1)) :
    Result R (n + 1) := Id.run do
  let (a, den) := x.split
  let dx := g.velocity D
  let k := poleOrder g den
  let p := parts D dx den k a
  let some (logs, corr) := Residue.logPart p.proper p.normalDen (Step.polyDer D dx p.normalDen)
      (dx.coeff 1) | return .nonelementary
  let rest := p.laurent + Poly.monomial k corr
  let result := match g with
    | .prim b => Kind.Prim.integrate lower b rest
    | .exp u => Kind.Exp.integrate D u lower rest k
  match result with
  | .nonelementary => return .nonelementary
  | .elementary ans => return .elementary (ans.add ⟨p.exactPart, logs⟩)

end Elementary

end SympyProofs.Calculus.Antiderivative
