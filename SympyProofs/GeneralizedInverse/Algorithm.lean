module

public import SympyProofs.Rref.Algorithm

/-! Imperative extraction of the canonical generalized inverse from augmented RREF. -/

@[expose] public section

namespace SympyProofs.GeneralizedInverse

open SympyProofs.Rref

variable {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}

/-- Reduce the full augmented matrix over `F` and return its canonical generalized
inverse as an `n × m` vector buffer. Augmentation and extraction are inlined. -/
def generalizedInverse (A : Vector (Vector F n) m) : Vector (Vector F m) n := Id.run do
  let augmented := Vector.ofFn fun i : Fin m => Vector.ofFn fun j : Fin (n + m) =>
    if h : j.val < n then A[i.val][j.val] else if j.val = n + i.val then 1 else 0
  let reduced := rref augmented
  let mut out : Vector (Vector F m) n := Vector.replicate n (Vector.replicate m 0)
  for i in List.finRange m do
    let some p := reduced.pivots[i.val] | continue
    if h : p.val ≥ n then
      continue
    else
      let row := reduced.rows[i.val]
      let mut values : Vector F m := Vector.replicate m 0
      for k in List.finRange m do
        values := values.set k.val row[n + k.val]
      out := out.set p.val values (Nat.lt_of_not_ge h)
  return out

end SympyProofs.GeneralizedInverse
