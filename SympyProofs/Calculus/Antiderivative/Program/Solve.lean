module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Program.Residue
public import SympyProofs.Calculus.Antiderivative.Program.Logarithmic
public import SympyProofs.Calculus.Antiderivative.Program.Step.Hermite
public import SympyProofs.Calculus.Antiderivative.Algebra.NatBound

/-! Parametric first-order differential equations in the newest tower generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- The derivative of the newest indeterminate, as a polynomial over the lower field. -/
def Gen.velocity (g : Gen (K R n)) (D : K R n → K R n) : Poly (K R n) :=
  match g with
  | .prim b => Poly.C b
  | .exp u => Poly.monomial 1 (D u)
  | .tan u => Poly.C (D u) * (1 + Poly.X ^ 2)

/-- Read the velocity of a polynomial step in the original tower field. -/
abbrev ReducedGen.velocity (g : ReducedGen (K R n)) (D : K R n → K R n) : Poly (K R n) :=
  (g : Gen (K R n)).velocity D

namespace Solve

/-- A constant-linear combination of polynomials. -/
def mix (cs : List (K R 0)) (ps : List (Poly (K R n))) : Poly (K R n) :=
  (cs.zipWith (fun c p => Poly.C (K.ofConst c) * p) ps).sum

/-- A linear combination of coordinate vectors of the given width. -/
def coordinates {F : Type} [Field F] (width : ℕ) (cs : List F) (vs : List (List F)) : List F :=
  (List.range width).map fun i => Linear.dot cs (vs.map (·.getD i 0))

/-- A vector of original parameters, a partial solution and its unsolved right-hand side. -/
structure Column (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    [Div R] (n : ℕ) where
  /-- Coordinates among the inputs to the original equation. -/
  params : List (K R 0)
  /-- Terms of the solution already found. -/
  solution : Poly (K R n)
  /-- Right-hand side after subtracting the operator applied to the partial solution. -/
  residual : Poly (K R n)

/-- Form a new column by a linear change of parameters. -/
def combine (width : ℕ) (vs : List (Column R n)) (c : List (K R 0)) : Column R n :=
  ⟨coordinates width c (vs.map Column.params), mix c (vs.map Column.solution),
    mix c (vs.map Column.residual)⟩

/-- Impose all coefficient equations of degree at least the cutoff on the residual. -/
def restrict (width lo : ℕ) (vs : List (Column R n)) : List (Column R n) :=
  let rows := ((coefficientSlices (vs.map Column.residual)).drop lo).flatMap rowsOf
  if rows.isEmpty then vs
  else (Linear.kernel rows vs.length).map (combine width vs)

/-- Add one monomial to a partial solution and subtract its image from the residual. -/
def extend (D : K R n → K R n) (dx a b : Poly (K R n)) (i : ℕ)
    (v : Column R n) (h : K R n) : Column R n :=
  let p := Poly.monomial i h
  {v with solution := v.solution + p, residual := v.residual - (a * Step.polyDer D dx p + b * p)}

/-- Solve the equation for the next coefficient and extend every resulting direction. -/
def extendSolutions (D : K R n → K R n) (dx a b : Poly (K R n)) (lower : Level R n)
    (width i : ℕ) (vs : List (Column R n)) (f : K R n) (gs : List (K R n)) :
    List (Column R n) :=
  let (hs, rows) := lower.solve f gs
  (Linear.kernel rows (vs.length + hs.length)).map fun q =>
    extend D dx a b i (combine width vs q) (Level.combine (q.drop vs.length) hs)

/-- Eliminate the coefficient of degree `degree + i` in the current residual. -/
def leadingStep (D : K R n → K R n) (dx a b : Poly (K R n)) (lower : Level R n)
    (width degree i : ℕ) (vs : List (Column R n)) : List (Column R n) :=
  let r := a.coeff degree
  let s := b.coeff degree + (i : K R n) * dx.coeff 1 * r
  let lead := fun v : Column R n => v.residual.coeff (degree + i)
  if r = 0 then vs.map fun v => extend D dx a b i v (lead v / s)
  else extendSolutions D dx a b lower width i vs (s / r) (vs.map fun v => lead v / r)

/-- Solve from the leading coefficient down, retaining a spanning family of pairs of
input vectors and partial solutions at each degree. -/
def descend (D : K R n → K R n) (dx a b : Poly (K R n)) (lower : Level R n)
    (width degree : ℕ) : ℕ → List (Column R n) → List (Column R n)
  | 0, vs => restrict width 0 vs
  | i + 1, vs =>
    descend D dx a b lower width degree i (leadingStep D dx a b lower width degree i vs)

/-- Bound the power of the exponential generator needed in a universal denominator. -/
def special (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (a b d : Poly (K R n)) : ℕ :=
  match g with
  | .prim _ => 0
  | .exp u =>
    max d.natDegree (if b.coeff 0 = 0 then 0 else
      exponentBound (lower.logRelations [-(a.coeff 0 / b.coeff 0), D u]))

/-- A bound on positive integral residues of the logarithmic derivative at normal poles. -/
def normalBound [NatBound (K R 0)] (a b db : Poly (K R n)) : ℕ :=
  if b.natDegree = 0 then 0
  else NatBound.natRootBound (Residue.constantRoots (Residue.residuePolynomial a b db))

/-- The next-to-leading coefficient obstruction for a primitive generator. -/
def cancellation (a b : Poly (K R n)) (degree : ℕ) : K R n :=
  if degree = 0 then 0 else
    (a.coeff (degree - 1) * b.coeff degree - a.coeff degree * b.coeff (degree - 1)) /
      a.coeff degree ^ 2

/-- A strict upper bound on the degree of a polynomial solution of the cleared equation. -/
def degreeBound [NatBound (K R 0)] (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (a b : Poly (K R n)) (degree size : ℕ) : ℕ :=
  let r := a.coeff degree
  match g with
  | .prim v =>
    if r = 0 then size + 2 else
      let m := (lower.limited (cancellation a b degree) v).map fun z => NatBound.natBound z.1
      max (size + 2) (m.getD 0 + 1)
  | .exp u =>
    if r = 0 then size else
      max size (exponentBound (lower.logRelations [b.coeff degree / r, D u]) + 1)

/-- Seed the coefficient solver with the original right-hand sides as independent parameters. -/
abbrev initial (rhs : List (Poly (K R n))) : List (Column R n) :=
  rhs.zipIdx.map fun (h, i) => Column.mk (Linear.unit rhs.length i) 0 h

/-- Combine the pole at the exponential generator with the normal pole bounds. -/
def denominator [NatBound (K R 0)] (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (num den d : Poly (K R n)) : Poly (K R n) :=
  Poly.X ^ special D g lower num den d * d *
    den ^ normalBound num den (Step.polyDer D (g.velocity D) den)

/-- All input directions and polynomial solutions after bounding the degree. -/
def polynomialSolutions [NatBound (K R 0)] (D : K R n → K R n) (g : ReducedGen (K R n))
    (lower : Level R n)
    (a b : Poly (K R n)) (rhs : List (Poly (K R n))) : List (Column R n) :=
  let degree := max a.natDegree b.natDegree
  let size := (rhs.map (·.coeffs.length)).max?.getD 0
  let bound := degreeBound D g lower a b degree size
  descend D (g.velocity D) a b lower rhs.length degree bound (initial rhs)

/-- Express the graph of a solution family by one constraint per original parameter. -/
def describe (width : ℕ) (p : Poly (K R n)) (cols : List (Column R n)) :
    List (K R (n + 1)) × List (List (K R 0)) :=
  (cols.map (fun v => K.join v.solution p),
    (List.range width).map fun i => Linear.unit width i ++ cols.map (fun v => -v.params.getD i 0))

/-- Solve the parametric equation at one tower step by clearing denominators and descending
through the coefficients of its polynomial numerator. -/
def step [NatBound (K R 0)] (D : K R n → K R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (f : K R (n + 1)) (gs : List (K R (n + 1))) : List (K R (n + 1)) × List (List (K R 0)) :=
  let (num, den) := f.split
  let (ws, d) := commonDen gs
  let p := denominator D g lower num den d
  let a := p * den
  let b := num * p - den * Step.polyDer D (g.velocity D) p
  let rhs := ws.map (· * ((p / d) * a))
  describe gs.length p (polynomialSolutions D g lower a b rhs)

end Solve

end SympyProofs.Calculus.Antiderivative
