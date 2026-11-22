module

public import SympyProofs.RealCubeRoot.Principal

/-!
# A modified principal cube root expressed without conditionals

With `η = (1 + i * sqrt(3)) / 2`, define
`modifiedPrincipal z = η * principal z + conj η * conj (principal (conj z))`.

This file contains the definition alone. Its properties are proved in
`Properties.lean`.
-/

@[expose] public section

noncomputable section

namespace RealCubeRoot

open Complex
open scoped ComplexConjugate

/-- A real-compatible cube root using only principal cube roots, conjugation,
and arithmetic, with no conditionals or variable denominators. -/
def modifiedPrincipal (z : ℂ) : ℂ :=
  let η : ℂ := (1 + (Real.sqrt 3 : ℂ) * I) / 2
  η * principal z + conj η * conj (principal (conj z))

end RealCubeRoot
