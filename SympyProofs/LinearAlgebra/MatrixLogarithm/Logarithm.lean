module

public import SympyProofs.LinearAlgebra.MatrixExponential.Basic

/-!
# Chosen matrix logarithms

`Logarithm A` records a matrix `L` together with a proof that `exp L = A`.
Adjoint and entrywise conjugation transport this certificate to the transformed
base. A certificate makes no assertion about the branch, existence, or uniqueness
of a principal logarithm.
The existence and uniqueness theorem and its canonical choice are provided by
`MatrixLogarithm.PrincipalLogarithm`.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A chosen matrix logarithm, with its defining equation. No branch is implicit. -/
structure Logarithm (A : Matrix n n ℂ) where
  val : Matrix n n ℂ
  exp_val : exp val = A

namespace Logarithm

variable {A : Matrix n n ℂ}

/-- The adjoint of the chosen logarithm is a logarithm of the adjoint base. -/
def adjoint (L : Logarithm A) : Logarithm Aᴴ where
  val := L.valᴴ
  exp_val := by rw [exp_conjTranspose, L.exp_val]

/-- Entrywise conjugation transports a chosen logarithm to the conjugate base. -/
def conjugate (L : Logarithm A) : Logarithm (A.map star) where
  val := L.val.map star
  exp_val := by rw [exp_map_star, L.exp_val]

end Logarithm

end SympyProofs.MatrixExponential
