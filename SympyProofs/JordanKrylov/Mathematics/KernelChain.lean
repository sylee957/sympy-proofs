import SympyProofs.JordanKrylov.Mathematics.Existence

/-!
# The ascending chain of kernels in Section 2

The kernels of powers of f(A) are subspaces over K. Their inclusions hold
for every polynomial and every natural exponent, so the definition does not
need a bound from the multiplicity of f in the minimal polynomial.
-/

namespace SympyProofs.JordanKrylov

open Polynomial Matrix

/-- The K-vector space ker(f(A)^ℓ). -/
noncomputable def powerKernel (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ : ℕ) :
    Submodule K (Fin n → K) :=
  LinearMap.ker ((aeval A f) ^ ℓ).mulVecLin

/-- The paper's defining condition for membership in ker(f(A)^ℓ). -/
@[simp] theorem mem_powerKernel (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ : ℕ) (u : Fin n → K) :
    u ∈ powerKernel K A f ℓ ↔ ((aeval A f) ^ ℓ) *ᵥ u = 0 := Iff.rfl

/-- At exponent zero, the kernel is the zero subspace {0}. -/
@[simp] theorem powerKernel_zero (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    powerKernel K A f 0 = ⊥ := by
  ext u
  simp

/-- Every vector killed by f(A)^ℓ is also killed by f(A)^(ℓ+1). -/
theorem powerKernel_le_succ (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (ℓ : ℕ) :
    powerKernel K A f ℓ ≤ powerKernel K A f (ℓ + 1) := by
  intro u hu
  rw [mem_powerKernel] at hu ⊢
  rw [pow_succ', ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]

/-- The kernels form an ascending chain of K-vector spaces. -/
theorem powerKernel_monotone (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    Monotone (powerKernel K A f) :=
  monotone_nat_of_le_succ (powerKernel_le_succ K A f)

/-- In particular, any two exponents in the paper's range give an inclusion. -/
theorem powerKernel_le (K : Subfield ℂ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) {ℓ m : ℕ} (h : ℓ ≤ m) :
    powerKernel K A f ℓ ≤ powerKernel K A f m :=
  powerKernel_monotone K A f h

end SympyProofs.JordanKrylov
