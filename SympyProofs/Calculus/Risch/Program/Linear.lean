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

/-- `u - c w` on the first `M` coordinates. A missing entry counts as `0`. -/
def vsub (M : Nat) (u : List Rat) (c : Rat) (w : List Rat) : List Rat :=
  (List.range M).map fun i => u.getD i 0 - c * w.getD i 0

/-- Impose the equation `r · x = 0` on a list of generators: one generator `w` that does not
satisfy it is removed, and every other generator `g` is replaced by `g - (r·g / r·w) w`. -/
def step (M : Nat) (r : List Rat) (G : List (List Rat)) : List (List Rat) :=
  match G.find? (fun g => dot r g != 0) with
  | none => G
  | some w => (G.erase w).map fun g => vsub M g (dot r g / dot r w) w

/-- Generators of the solutions in `M` unknowns of all the equations. -/
def kernel (rows : List (List Rat)) (M : Nat) : List (List Rat) :=
  rows.foldl (fun G r => step M r G) ((List.range M).map (unit M))

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
