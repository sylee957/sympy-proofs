import SympyProofs.JordanKrylov.Algorithms.JordanKrylovElimination

/-! # Procedure 4: reduction of a generating layer -/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- Find the first vanishing power, up to the supplied bound. -/
def boundedVectorRank {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : (Fin n → K) → (Fin n → K)) (v : Fin n → K) (bound : ℕ) : ℕ :=
  Id.run do
    let mut w := v
    for j in List.range bound do
      w := F w
      if w = 0 then
        return j + 1
    return 0

/-- Procedure 4: reduce the highest remaining layer and redistribute its ranks. -/
def reduceKrylovGenerators {K : Type} [Field K] [DecidableEq K] {n : ℕ}
    (F : (Fin n → K) → (Fin n → K))
    (V : ℕ → List (Fin n → K)) (ℓ : ℕ) : ℕ → List (Fin n → K) := Id.run do
  let mut D : Array (Fin n × (Fin n → K)) := #[]
  for v in V ℓ do
    let mut r := v
    for (i, w) in D do
      r := r - (r i / w i) • w
    for i in List.finRange n do
      if r i ≠ 0 then
        D := D.push (i, r)
        break
  let columns := D.toList.map Prod.snd
  let mut pending := Function.update V ℓ []
  for v in columns do
    if v ≠ 0 then
      let rank := boundedVectorRank F v ℓ
      pending := Function.update pending rank (pending rank ++ [v])
  return pending

end SympyProofs.JordanKrylov
