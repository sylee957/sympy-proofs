import SympyProofs.JordanKrylov.Algorithms.ReduceKrylovGenerators

/-! # Algorithm 3: refined Jordan–Krylov elimination

The table stores the simultaneous columns of `W` and `S`. Terminal vectors are
computed on demand. `used` is the complement of the paper's counter `m'`:
accepting rank `ℓ` adds `ℓ`, and `used = m` is the stopping test.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Descending elimination with on-demand terminal vectors and rank-sum stopping.
The two recursion measures are the current rank and the remaining layer length. -/
def refinedElimination (K : Type) [Field K] [DecidableEq K] [PolynomialOperations K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (m : ℕ)
    (ℓ : ℕ) (todo : List (Fin n → K)) (pending : ℕ → List (Fin n → K))
    (basis : Finset (Fin n → K)) (used : ℕ)
    (D : Array (Fin n × PairedColumn K n)) : Finset (Fin n → K) := Id.run do
  match ℓ, todo with
  | 0, _ => return basis
  | k + 1, [] =>
    if k = 0 then return basis
    let D := D.map (fun (i, w) => (i, { top := w.top, bottom := PolynomialOperations.applyMatrix f A w.bottom }))
    return refinedElimination K A f m k (pending k) (Function.update pending k []) basis used D
  | k + 1, v :: rest =>
    let F := PolynomialOperations.applyMatrix f A
    let mut top := v
    for _ in List.range k do
      top := F top
    let r := reducePairedColumn D { top := top, bottom := v }
    if r.top ≠ 0 then
      let basis := insert r.bottom basis
      let used := used + (k + 1)
      if used = m then return basis
      let mut D := D
      let mut w := r
      for _ in List.range f.natDegree do
        D := insertPairedColumn D w
        w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
      return refinedElimination K A f m (k + 1) rest pending basis used D
    else if r.bottom ≠ 0 ∧ 1 < k + 1 then
      let rank := boundedVectorRank F r.bottom k
      let pending := Function.update pending rank (pending rank ++ [r.bottom])
      return refinedElimination K A f m (k + 1) rest pending basis used D
    else
      return refinedElimination K A f m (k + 1) rest pending basis used D
termination_by (ℓ, todo.length)

/-- Algorithm 3, optionally preceded by Procedure 4 at the highest layer.
The same verified reduction may also be used separately on lower layers. -/
def computeRefinedJordanKrylovBasis (K : Type) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) (preprocess : Bool := false) :
    Finset (Fin n → K) :=
  let V := fun j => if 1 ≤ j ∧ j ≤ ℓbar then V j else []
  let V := if preprocess then reduceKrylovGenerators (PolynomialOperations.applyMatrix f A) V ℓbar
    else V
  refinedElimination K A f m ℓbar (V ℓbar) (Function.update V ℓbar []) ∅ 0 #[]

end SympyProofs.JordanKrylov
