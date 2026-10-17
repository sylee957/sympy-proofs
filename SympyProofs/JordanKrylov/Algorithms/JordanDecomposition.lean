import SympyProofs.JordanKrylov.Algorithms.MinimalAnnihilatingPolynomials
import SympyProofs.JordanKrylov.Algorithms.GeneralizedEigenspace

/-! End-to-end symbolic Jordan decomposition. Root selection is deferred to interpretation. -/
namespace SympyProofs.JordanKrylov
open Matrix Polynomial

/-- One primary component. Chains run from the highest generalized eigenvector
 to the eigenvector. Every root of `factor` receives the same chain lengths. -/
structure SymbolicJordanComponent (K : Type) [Field K] (n : ℕ) where
  factor : K[X]
  multiplicity : ℕ
  chains : Finset (List (Fin n → K[X]))

/-- Factor the characteristic polynomial, compute all coordinate-vector minimal
annihilators once, then assemble symbolic chains for every primary component.
Algorithm 7 uses distinguished factor `X` with bound zero: all factors, including
any copies of `X`, are handled by its general factor search. -/
def computeJordanDecomposition (K : Type) [Field K] [DecidableEq K]
    [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool := false) :
    Array (SymbolicJordanComponent K n) := Id.run do
  let factors := Operations.factorCharpoly A
  let mut expanded := #[]
  for (f, m) in factors do
    for _ in List.range m do
      expanded := expanded.push f
  let e := fun i : Fin n => fun j : Fin n => if i = j then (1 : K) else 0
  let annihilators := computeMinimalAnnihilatingPolynomials K A Operations.indeterminate 0 expanded e
  have annihilators_size : annihilators.size = n :=
    computeMinimalAnnihilatingPolynomials_size K A Operations.indeterminate 0 expanded e
  let p := fun i : Fin n =>
    annihilators[i.val]'(Nat.lt_of_lt_of_eq i.isLt annihilators_size.symm)
  let mut components := #[]
  for (f, m) in factors do
    let chains := computeGeneralizedEigenspace K A f e p m preprocess
    components := components.push ⟨f, m, chains⟩
  return components

end SympyProofs.JordanKrylov
