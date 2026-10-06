import SympyProofs.ComplexRouthHurwitz.Reference.Correctness
import SympyProofs.ComplexRouthHurwitz.FractionFree.Correctness
import SympyProofs.ComplexRouthHurwitz.Exact.Correctness

/-! Direct complex Routh interfaces and coefficient-domain foundations.

`Reference` contains the field-division runner and its capstones; `Table` contains
shared row mathematics. `FractionFree` separates the ring identities, the
previous-squared-pivot field runner, its loop invariant, and its capstones.
`Exact.Gaussian.run` computes in Gaussian integers using Mathlib's ring and
conjugation structures. Its loop invariant proves every reached division exact,
including after repairs, and transports root counts and stability to the complex
denotation.
-/
