import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilators
import SympyProofs.JordanKrylov.Algorithms.PrimaryGenerating
import SympyProofs.JordanKrylov.Algorithms.RefinedJordanKrylovBasis
import SympyProofs.JordanKrylov.Algorithms.JordanChains

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
The factor-only annihilator search handles all irreducible factors uniformly. -/
def computeJordanDecomposition (K : Type) [Field K] [DecidableEq K]
    [Operations K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (preprocess : Bool := false) :
    Array (SymbolicJordanComponent K n) := Id.run do
  let factors := Operations.factorCharpoly A
  let e := fun i : Fin n => fun j : Fin n => if i = j then (1 : K) else 0
  let annihilators := computeBasisAnnihilators K A factors e
  have annihilators_size : annihilators.size = n :=
    computeBasisAnnihilators_size K A factors e
  let p := fun i : Fin n =>
    annihilators[i.val]'(Nat.lt_of_lt_of_eq i.isLt annihilators_size.symm)
  let mut components := #[]
  for (f, m) in factors do
    let ℓbar := Finset.univ.sup (fun i => Operations.multiplicity f (p i))
    -- Algorithm 1: primary generators grouped by rank.
    let V := computePrimaryGenerators K A e f p
    -- Algorithm 3: refine the generators to a Jordan–Krylov basis.
    let B := computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess
    -- Algorithm 5: assemble the symbolic Jordan chains.
    let chains := computeJordanChains K A f B ℓbar
    components := components.push ⟨f, m, chains⟩
  return components

end SympyProofs.JordanKrylov
