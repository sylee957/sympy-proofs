import SympyProofs.LinearAlgebra.MatrixFunction.Interpolation
import SympyProofs.LinearAlgebra.MatrixFunction.Primary
import SympyProofs.LinearAlgebra.MatrixFunction.Hermite
import SympyProofs.LinearAlgebra.MatrixFunction.JordanBlock

/-!
# Primary matrix functions

Reusable polynomial interpolation and evaluation on generalized eigenspaces.
The construction retains nilpotent information and is independent of the
interpolating polynomial chosen. It underlies the logarithm and power APIs.
`Hermite` reduces interpolants modulo the matrix's minimal polynomial and proves
uniqueness of the resulting polynomial below that degree.
-/
