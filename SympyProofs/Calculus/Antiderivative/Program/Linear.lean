module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Homogeneous linear systems over the constant field, with missing coordinates equal to zero. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Linear

variable {F : Type} [Field F]

/-- The sum of products of matching coordinates. -/
def dot (a b : List F) : F := (List.zipWith (· * ·) a b).sum

/-- The `i`th coordinate vector in dimension `m`. -/
def unit (m i : ℕ) : List F := (List.range m).map fun j => if j = i then 1 else 0

/-- Remove a pivot coordinate from a row by subtracting a multiple of the pivot row. -/
def eliminateAt (pivot : List F) (i width : ℕ) (r : List F) : List F :=
  let factor := r.getD i 0 / pivot.getD i 0
  (List.range width).map fun j => r.getD j 0 - factor * pivot.getD j 0

variable [DecidableEq F]

/-- Project a homogeneous system onto its first `m` coordinates by eliminating the next one. -/
def eliminate (m : ℕ) (rows : List (List F)) : List (List F) :=
  match rows.find? (fun r => r.getD m 0 != 0) with
  | none => rows.map (List.take m)
  | some pivot => rows.map (eliminateAt pivot m m)

/-- A basis of the kernel, obtained by eliminating the last unknown and back-substituting. -/
def kernel (rows : List (List F)) (width : ℕ) : List (List F) :=
  match width with
  | 0 => []
  | m + 1 =>
    match rows.find? (fun r => r.getD m 0 != 0) with
    | none =>
      unit (m + 1) m :: (kernel (rows.map (List.take m)) m).map (· ++ [0])
    | some pivot =>
      (kernel (rows.map (eliminateAt pivot m m)) m).map fun v =>
        v ++ [-dot pivot v / pivot.getD m 0]

/-- A solution with first coordinate one, when the kernel contains one. -/
def normalized (rows : List (List F)) (width : ℕ) : Option (List F) := do
  let v ← (kernel rows width).find? fun w => w.headD 0 != 0
  return v.map (· / v.headD 0)

end SympyProofs.Calculus.Antiderivative.Linear
