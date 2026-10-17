import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilatorsCorrectness
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
  let raw := computeBasisAnnihilators K A factors e
  have bounds := computeBasisAnnihilators_sizes K A factors e
  let polynomials : Vector K[X] n := ⟨raw.1, bounds.1⟩
  let mut components := #[]
  for j in List.finRange factors.size do
    let (f, m) := factors[j.val]
    let column := raw.2[j.val]'(Nat.lt_of_lt_of_eq j.isLt bounds.2.1.symm)
    let ranks : Vector ℕ n := ⟨column, bounds.2.2 column (Array.getElem_mem _)⟩
    -- Algorithm 1: primary generators and maximum rank from cached exponents.
    let (V, ℓbar) := computePrimaryGenerators K A e f polynomials ranks
    -- Algorithm 3: refine the generators to a Jordan–Krylov basis.
    let B := computeRefinedJordanKrylovBasis K A f V ℓbar m preprocess
    -- Algorithm 5: assemble the symbolic Jordan chains.
    let chains := computeJordanChains K A f B ℓbar
    components := components.push ⟨f, m, chains⟩
  return components

end SympyProofs.JordanKrylov
