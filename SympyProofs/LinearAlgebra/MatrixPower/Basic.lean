module

public import SympyProofs.LinearAlgebra.MatrixLogarithm.Logarithm

/-!
# Matrix powers relative to a chosen logarithm

A power formed from a chosen logarithm `L` is `exp (z • L)`. Its adjoint uses the
logarithm `Lᴴ`, and its entrywise conjugate uses `L.map star`. These are logarithms
of the transformed base, but need not be its principal logarithms.

These results hold for arbitrary finite complex matrices with a supplied logarithm.
They do not select a principal logarithm. General principal powers and their
branch conditions are proved in `MatrixPower.Principal`. The extension
to all invertible matrices, including negative eigenvalues, is defined in
`MatrixPower.HalfOpen`; diagonal formulas are available in
`MatrixPower.Diagonal`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Logarithm

variable {A : Matrix n n ℂ}

/-- Complex powers relative to a fixed logarithm of the base. -/
noncomputable def cpow (L : Logarithm A) (z : ℂ) : Matrix n n ℂ :=
  exp (z • L.val)

@[simp] theorem cpow_zero (L : Logarithm A) : L.cpow 0 = 1 := by
  simp [cpow]

@[simp] theorem cpow_one (L : Logarithm A) : L.cpow 1 = A := by
  simpa only [cpow, one_smul] using L.exp_val

theorem cpow_natCast (L : Logarithm A) (k : ℕ) : L.cpow (k : ℂ) = A ^ k := by
  rw [cpow, exp_natCast_smul, L.exp_val]

theorem conjTranspose_cpow (L : Logarithm A) (z : ℂ) :
    (L.cpow z)ᴴ = L.adjoint.cpow (star z) :=
  conjTranspose_exp_smul L.val z

theorem map_star_cpow (L : Logarithm A) (z : ℂ) :
    (L.cpow z).map star = L.conjugate.cpow (star z) :=
  map_star_exp_smul L.val z

end Logarithm

end SympyProofs.MatrixExponential
