import SympyProofs.LambertW.Complex.Boundary.Branches.Matching
import SympyProofs.LambertW.Complex.Boundary.Branches.Conjugation
import SympyProofs.LambertW.Complex.Boundary.Branches.Definitions
import SympyProofs.LambertW.Complex.Boundary.Branches.Compatibility
import SympyProofs.LambertW.Complex.Boundary.Branches.Expansions

/-!
# Indexed Lambert W with boundary values

Use `LambertW.Complex.branchWithBoundary k side z` for every indexed branch.
The side is `.upper` or `.lower`. Both agree with `branch k` off the cut.
At zero only index zero has a specified continuous extension.
Specialized constructions in `Boundary.Internal` are proof models, not public conventions.
-/
