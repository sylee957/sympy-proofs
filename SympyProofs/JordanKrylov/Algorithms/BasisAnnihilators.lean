import SympyProofs.JordanKrylov.Algorithms.Operations
import Std.Tactic.Do
import Std.WP

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Compute minimal annihilators directly from factor/multiplicity pairs.
For each vector, isolate each remaining factor with the complementary product,
then determine its required exponent by successive applications of that factor.
The factorization is never expanded into repeated polynomial entries. -/
def computeBasisAnnihilators (K : Type*) [Field K] [DecidableEq K]
    [Operations K] {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (factors : Array (K[X] × ℕ)) (e : Fin m → (Fin n → K)) : Array K[X] := Id.run do
  let mut result : Array K[X] := #[]
  for i in List.finRange m do
    let mut b0 := e i
    let mut candidate := Operations.one
    let mut remaining := factors.toList
    for (f, exponent) in factors do
      if b0 = 0 then break
      remaining := remaining.tail
      let mut cofactor := Operations.one
      for (g, multiplicity) in remaining do
        cofactor := Operations.mul cofactor (Operations.pow g multiplicity)
      let mut probe := if remaining.isEmpty then b0 else Operations.applyMatrix cofactor A b0
      for _ in List.range exponent do
        if probe = 0 then break
        probe := Operations.applyMatrix f A probe
        b0 := Operations.applyMatrix f A b0
        candidate := Operations.mul candidate f
    result := result.push candidate
  return result

open scoped Std.WP in
/-- The routine returns one polynomial per input vector, in input order. -/
theorem computeBasisAnnihilators_size
    (K : Type*) [Field K] [DecidableEq K] [Operations K] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (factors : Array (K[X] × ℕ))
    (e : Fin m → (Fin n → K)) :
    (computeBasisAnnihilators K A factors e).size = m := by
  generalize h : computeBasisAnnihilators K A factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ out => out.size = pref.length
  · fun _ _ _ => True
  · fun _ _ _ => True
  · fun _ _ _ => True
  all_goals simp_all [result]

end SympyProofs.JordanKrylov
