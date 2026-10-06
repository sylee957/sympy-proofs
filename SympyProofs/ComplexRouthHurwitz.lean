import SympyProofs.ComplexRouthHurwitz.Reference.Correctness
import SympyProofs.ComplexRouthHurwitz.FractionFree.Correctness
import SympyProofs.ComplexRouthHurwitz.Exact.Correctness

/-! Direct complex Routh interfaces and coefficient-domain foundations.

`Reference` contains the field-division runner and its capstones; `Table` contains
shared row mathematics. `FractionFree` separates the ring identities, the
previous-squared-pivot field runner, its loop invariant, and its capstones.
`Exact.Gaussian.run` accepts Gaussian-integer polynomials but stores each
alternating real/imaginary row as `Vector ℤ`. Degree parity supplies the omitted
factor of `i`; ordinary elimination uses integer arithmetic and exact integer
division. Reciprocal repairs temporarily use Gaussian coordinates. `Exact.Model`
contains only shared Gaussian row operations and one-step arithmetic lemmas. The
integer loop invariant proves exact division, root counts, and stability; there
is no separate Gaussian runner.
-/
