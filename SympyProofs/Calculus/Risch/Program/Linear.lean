module

/-! Linear algebra over the rationals. A vector is a list of rationals, and a homogeneous
linear system is a list of rows, each row `r` standing for the equation `r · x = 0`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Linear

/-- The sum of the products of corresponding entries, up to the shorter length. -/
def dot (row xs : List Rat) : Rat := (List.zipWith (· * ·) row xs).sum

/-- The `i`th unit vector of length `m`. -/
def unit : Nat → Nat → List Rat
  | 0, _ => []
  | m + 1, 0 => 1 :: List.replicate m 0
  | m + 1, i + 1 => 0 :: unit m i

/-! The kernel is computed over the integers: Lean's rational arithmetic finds a greatest
common divisor after every operation, through GMP even for small numbers. -/

/-- A row with the same equation and integer entries: multiplied by the least common
multiple of the denominators. -/
def intRow (r : List Rat) : List Int :=
  if r.all (·.den == 1) then r.map (·.num)
  else
    let d : Nat := r.foldl (fun acc q => Nat.lcm acc q.den) 1
    r.map fun q => q.num * ((d / q.den : Nat) : Int)

def dotZ (r g : List Int) : Int := (List.zipWith (· * ·) r g).foldl (· + ·) 0

/-- A generator with the same span, divided by the greatest common divisor of its entries
once they grow large. -/
def smallZ (g : List Int) : List Int :=
  if g.all fun a => a.natAbs < 2 ^ 60 then g
  else
    let c : Int := (g.foldl (fun acc a => Nat.gcd acc a.natAbs) 0 : Nat)
    if c ≤ 1 then g
    else if g.all fun a => a % c == 0 then g.map (· / c) else g

/-- The `i`th unit vector of length `m`, with integer entries. -/
def unitZ : Nat → Nat → List Int
  | 0, _ => []
  | m + 1, 0 => 1 :: List.replicate m 0
  | m + 1, i + 1 => 0 :: unitZ m i

/-- Impose the equation `r · x = 0` on a list of generators: one generator `w` that does not
satisfy it is removed, and every other generator `g` is replaced by `(r·w) g - (r·g) w`. -/
def stepZ (r : List Int) (G : List (List Int)) : List (List Int) :=
  match G.find? (fun g => dotZ r g != 0) with
  | none => G
  | some w =>
    let rw := dotZ r w
    (G.erase w).map fun g =>
      let c := dotZ r g
      smallZ (List.zipWith (fun a b => rw * a - c * b) g w)

/-- Generators of the solutions in `M` unknowns of all the equations. -/
def kernel (rows : List (List Rat)) (M : Nat) : List (List Rat) :=
  let G := (rows.map intRow).foldl (fun G r => stepZ r G) ((List.range M).map (unitZ M))
  G.map fun g => g.map fun (a : Int) => (a : Rat)

/-- `b r - c p` on the first `m` coordinates. -/
def reduceRow (m : Nat) (b : Rat) (r : List Rat) (c : Rat) (p : List Rat) : List Rat :=
  (List.range m).map fun i => b * r.getD i 0 - c * p.getD i 0

/-- Eliminate the unknown at position `m` from a homogeneous system, using one row whose
entry at position `m` is not zero. -/
def eliminate (m : Nat) (rows : List (List Rat)) : List (List Rat) :=
  match rows.find? (fun r => r.getD m 0 != 0) with
  | none => rows
  | some p => rows.map fun r => reduceRow m (p.getD m 0) r (r.getD m 0) p

/-- A solution in `M` unknowns whose first coordinate is `1`, if there is one. -/
def normalized (rows : List (List Rat)) (M : Nat) : Option (List Rat) :=
  match (kernel rows M).find? (fun g => g.getD 0 0 != 0) with
  | none => none
  | some g => some (g.map fun a => a / g.getD 0 0)

end SympyProofs.Calculus.Risch.Linear
