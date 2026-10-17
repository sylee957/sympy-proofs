import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilators
import SympyProofs.JordanKrylov.Algorithms.MinimalAnnihilatingPolynomialsCorrectness

namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- A full annihilating product of monic irreducibles suffices for the
factor-only search to compute the minimal annihilator of every input vector. -/
theorem computeBasisAnnihilators_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (factors : Array K[X]) (e : Fin m → (Fin n → K))
    (hg : ∀ g ∈ factors, g.Monic ∧ Irreducible g)
    (hann : aeval A factors.toList.prod = 0) :
    computeBasisAnnihilators K A factors e =
      Array.ofFn (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  rw [computeBasisAnnihilators_eq]
  apply computeMinimalAnnihilatingPolynomials_correct K hops A X 0 factors e
    monic_X irreducible_X hg
  simpa only [pow_zero, one_mul] using hann

end SympyProofs.JordanKrylov
