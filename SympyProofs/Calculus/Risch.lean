module

public import SympyProofs.Calculus.Risch.Program.Term
public import SympyProofs.Calculus.Risch.Program.Normal
public import SympyProofs.Calculus.Risch.Program.Poly
public import SympyProofs.Calculus.Risch.Program.Linear
public import SympyProofs.Calculus.Risch.Program.Constraints
public import SympyProofs.Calculus.Risch.Program.Deriv
public import SympyProofs.Calculus.Risch.Program.Resultant
public import SympyProofs.Calculus.Risch.Program.Rel
public import SympyProofs.Calculus.Risch.Program.Solve
public import SympyProofs.Calculus.Risch.Program.Admissible
public import SympyProofs.Calculus.Risch.Program.Hermite
public import SympyProofs.Calculus.Risch.Program.Answer
public import SympyProofs.Calculus.Risch.Program.PolyPart
public import SympyProofs.Calculus.Risch.Program.Residue
public import SympyProofs.Calculus.Risch.Program.Integrate
public import SympyProofs.Calculus.Risch.Spec.Field
public import SympyProofs.Calculus.Risch.Spec.Poly
public import SympyProofs.Calculus.Risch.Spec.Linear
public import SympyProofs.Calculus.Risch.Spec.Derivation
public import SympyProofs.Calculus.Risch.Spec.Admissible
public import SympyProofs.Calculus.Risch.Spec.Solve
public import SympyProofs.Calculus.Risch.Spec.Elementary
public import SympyProofs.Calculus.Risch.Spec.Answer
public import SympyProofs.Calculus.Risch.Spec.Liouville
public import SympyProofs.Calculus.Risch.Algebra.SimplePole
public import SympyProofs.Calculus.Risch.Algebra.HermiteLemmas
public import SympyProofs.Calculus.Risch.Algebra.ResidueLemmas
public import SympyProofs.Calculus.Risch.Algebra.CoprimeCover
public import SympyProofs.Calculus.Risch.Algebra.LogPart
public import SympyProofs.Calculus.Risch.Proof.Derivative
public import SympyProofs.Calculus.Risch.Proof.Normal
public import SympyProofs.Calculus.Risch.Proof.Poly
public import SympyProofs.Calculus.Risch.Proof.Linear
public import SympyProofs.Calculus.Risch.Proof.Constraints
public import SympyProofs.Calculus.Risch.Proof.Deriv
public import SympyProofs.Calculus.Risch.Proof.Constants
public import SympyProofs.Calculus.Risch.Proof.Pole
public import SympyProofs.Calculus.Risch.Proof.Subresultant
public import SympyProofs.Calculus.Risch.Proof.Resultant
public import SympyProofs.Calculus.Risch.Proof.SolvePoly
public import SympyProofs.Calculus.Risch.Proof.Rel
public import SympyProofs.Calculus.Risch.Proof.SolvePieces
public import SympyProofs.Calculus.Risch.Proof.Hermite
public import SympyProofs.Calculus.Risch.Proof.SolveBounds
public import SympyProofs.Calculus.Risch.Proof.SolveStep
public import SympyProofs.Calculus.Risch.Proof.Solve
public import SympyProofs.Calculus.Risch.Proof.Elementary
public import SympyProofs.Calculus.Risch.Proof.Answer
public import SympyProofs.Calculus.Risch.Proof.LiouvilleForm
public import SympyProofs.Calculus.Risch.Proof.PolyPart
public import SympyProofs.Calculus.Risch.Proof.ResidueDefs
public import SympyProofs.Calculus.Risch.Proof.ResidueCriterion
public import SympyProofs.Calculus.Risch.Proof.ConstRoots
public import SympyProofs.Calculus.Risch.Proof.GcdMod
public import SympyProofs.Calculus.Risch.Proof.RootSums
public import SympyProofs.Calculus.Risch.Proof.Residue
public import SympyProofs.Calculus.Risch.Proof.Integrate

/-!
# Elementary integration in towers of exponentials and logarithms

A decision procedure for elementary integration following Risch (1969), with its
specification. The design, the conventions and the state of the development are described in
`Risch/README.md`.

* `Program/` holds the algorithms: total functions on plain data, with no propositions and
  no dependency on Mathlib. `integrate` is the entry point, `integrateChecked` also tests
  the input conditions.
* `Spec/` defines what the data mean: the field of a tower over a constant field, its
  derivation, admissible towers, and what it means to solve the parametric equation.
* `Algebra/` holds lemmas about polynomials and rational functions over an arbitrary field.
* `Proof/` holds the specification of each program.

## Main theorems

For a tower `t` with `admissible t = true` and a term `f` with `f.defined = true`, over an
algebraically closed constant field `k` of characteristic zero:

* `integrate_sound`: if `integrate t f = .elementary a`, then `a` is defined in the field
  and its derivative is `f`;
* `integrate_complete`: if `integrate t f = .nonelementary`, then `f` is not of the form
  `v′ + Σ cᵢ uᵢ′ / uᵢ` with `v`, `uᵢ` in the field and constants `cᵢ`;
* `integrate_no_primitive`: in that case `f` has no primitive in any elementary extension
  of the field (Liouville's theorem).

`admissible_sound` says that an accepted tower is admissible over every constant field of
characteristic zero, and `solve_spec` is part (b) of Risch's Main Theorem for it.
`integrateChecked_sound` and `integrateChecked_complete` restate the main theorems for the
program that tests both input conditions itself.
-/
