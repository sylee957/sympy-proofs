import SympyProofs.JordanKrylov.Algorithms.ReduceKrylovGenerators

/-! # Algorithm 3: refined Jordan–Krylov elimination

The table stores the simultaneous columns of `W` and `S`. Terminal vectors are
computed on demand. `used` is the complement of the paper's counter `m'`:
accepting rank `ℓ` adds `ℓ`, and `used = m` is the stopping test.
-/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Algorithm 3, returning generators by rank, with optional Procedure 4
preprocessing at each nonempty layer. -/
def computeRefinedJordanKrylovBasis (K : Type) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) (preprocess : Bool := false) :
    (ℕ → Finset (Fin n → K)) := Id.run do
  let F := PolynomialOperations.applyMatrix f A
  let mut pending := fun j => if 1 ≤ j ∧ j ≤ ℓbar then V j else []
  if preprocess then
    pending := reduceKrylovGenerators F pending ℓbar
  let mut basis : ℕ → Finset (Fin n → K) := fun _ => ∅
  let mut used := 0
  let mut D : Array (Fin n × PairedColumn K n) := #[]
  -- Lines 2–5: select the first generator and test the singleton case immediately.
  if let v :: rest := pending ℓbar then
    pending := Function.update pending ℓbar rest
    basis := Function.update basis ℓbar {v}
    used := ℓbar
    if used = m then return basis
    -- Line 6: construct the initial simultaneous Krylov columns of W and S.
    let mut top := v
    for _ in List.range (ℓbar - 1) do
      top := F top
    let mut w : PairedColumn K n := { top := top, bottom := v }
    D := insertPairedColumn D w
    for _ in List.range (f.natDegree - 1) do
      w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
      D := insertPairedColumn D w
  for ℓ in (List.range ℓbar).reverse.map Nat.succ do
    -- Lines 8–10: simplify each nonempty lower layer before elimination.
    if preprocess ∧ ℓ < ℓbar ∧ pending ℓ ≠ [] then
      pending := reduceKrylovGenerators F pending ℓ
    let layer := pending ℓ
    pending := Function.update pending ℓ []
    -- Lines 11–14: consume candidates and reduce both halves together.
    for v in layer do
      let mut top := v
      for _ in List.range (ℓ - 1) do
        top := F top
      let r := reducePairedColumn D { top := top, bottom := v }
      if r.top ≠ 0 then
        -- Lines 15–20: accept a generator and stop when its rank completes m.
        basis := Function.update basis ℓ (insert r.bottom (basis ℓ))
        used := used + ℓ
        if used = m then return basis
        let mut w := r
        D := insertPairedColumn D w
        for _ in List.range (f.natDegree - 1) do
          w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
          D := insertPairedColumn D w
      else if r.bottom ≠ 0 ∧ 1 < ℓ then
        -- Lines 21–22: move the residual to its lower rank layer.
        let rank := boundedVectorRank F r.bottom (ℓ - 1)
        pending := Function.update pending rank (pending rank ++ [r.bottom])
    -- Lines 25–27: advance S to the next rank, leaving W unchanged.
    if 1 < ℓ then
      D := D.map (fun (i, w) =>
        (i, { top := w.top, bottom := F w.bottom }))
  return basis

end SympyProofs.JordanKrylov
