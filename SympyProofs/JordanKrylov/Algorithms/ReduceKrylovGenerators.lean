import SympyProofs.JordanKrylov.Algorithms.JordanKrylovElimination

/-! # Procedure 4: reduction of a generating layer -/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Find the first vanishing power, up to the supplied bound. -/
def boundedVectorRank {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (v : Fin n → K) (bound : ℕ) : ℕ :=
  (Id.run do
    let mut rank := 0
    let mut terminal := v
    let mut w := v
    for j in List.range bound do
      if rank = 0 then
        let next := F w
        if next = 0 then
          rank := j + 1
          terminal := w
        else
          w := next
    return (rank, terminal, w)).1

/-- Ordinary column reduction, retaining only independent nonzero columns. -/
def reduceGeneratorColumns {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (vs : List (Fin n → K)) : List (Fin n → K) := Id.run do
  let mut D : Array (Fin n × PairedColumn K n) := #[]
  for v in vs do
    D := insertPairedColumn D { top := v, bottom := v }
  return D.toList.map (fun iw => iw.2.top)

/-- Procedure 4: reduce the highest remaining layer and redistribute its ranks. -/
def reduceKrylovGenerators {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : (Fin n → K) → (Fin n → K))
    (V : ℕ → List (Fin n → K)) (ℓ : ℕ) : ℕ → List (Fin n → K) := Id.run do
  let columns := reduceGeneratorColumns (V ℓ)
  let mut pending := Function.update V ℓ []
  for v in columns do
    if v ≠ 0 then
      let rank := boundedVectorRank F v ℓ
      pending := Function.update pending rank (pending rank ++ [v])
  return pending

end SympyProofs.JordanKrylov
