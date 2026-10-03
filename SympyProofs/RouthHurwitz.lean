import SympyProofs.RouthHurwitz.Imperative.Correctness
import SympyProofs.RouthHurwitz.Exact.Correctness
import SympyProofs.RouthHurwitz.Exact.Polynomial
import SympyProofs.RouthHurwitz.Parametric.Correctness

/-!
# Three verified Routh–Hurwitz interfaces

* `Imperative.run`: the reference Routh table over real coefficients. Its
  correctness theorems count complex roots and characterize strict stability.
* `Exact.run`: fraction-free numeric arithmetic in a coefficient domain, using
  exact quotients and Mathlib ordered-ring comparisons. `Exact.RealDomain`
  supplies a compatible real embedding for correctness proofs. Integer and rational models are
  provided; the runtime never converts its rows to real or rational coefficients.
* `Parametric.run`: one unsigned previous-pivot pass returns the generated
  rows and a conjunction of strict inequalities. It holds exactly when the specialized leading
  coefficient is nonzero and the specialized polynomial is Hurwitz stable.

`Div` supplies division; `MulDivCancelClass` certifies cancellation on exact products.
Backends cover Euclidean domains, polynomial rings, and finite multivariate
polynomial rings. Open scoped `RouthHurwitz.Exact` to enable the polynomial
backends; existing Mathlib field-coefficient division takes priority.
Mathlib polynomial arithmetic is noncomputable for code
extraction; the polynomial backend is explicit leading-term cancellation.

`Parametric.run` contains the order-free certificate loop. `Parametric.Invariant`
relates its rows to Hurwitz minors and proves every reached division exact. `FractionFree.Stability`
connects those minors to the shared root mathematics. The other `FractionFree`
modules provide the verified real model used to transport numeric correctness.
`Table` contains local row mathematics and the semantic loop invariant; `Roots`
contains complex root-count and continuity lemmas.
-/
