module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.Matrix

import Mathlib.Analysis.Matrix.Normed

/-! Scalar derivatives of matrix-valued functions with a real or complex parameter,
characterized entrywise. The entries may lie in any normed space over the parameter
field. The statements use the usual matrix topology and do not export a
choice of matrix norm. Norm independence for finite matrices is in `Norms`. -/

@[expose] public section

namespace SympyProofs.MatrixDerivative

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- A matrix has scalar derivative `D` exactly when each entry has the
corresponding entry of `D` as its scalar derivative. Neither index type needs
to be finite: this uses the product topology on matrices. -/
theorem hasDerivAt_iff_entrywise {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : 𝕜 → Matrix m n E} {D : Matrix m n E} {t : 𝕜} :
    HasDerivAt M D t ↔ ∀ i j, HasDerivAt (fun s => M s i j) (D i j) t := by
  change HasDerivAt (fun s i j => M s i j) (fun i j => D i j) t ↔ _
  simp only [HasDerivAt, HasDerivAtFilter, hasFDerivAtFilter_iff_isLittleOTVS,
    Asymptotics.isLittleOTVS_pi]
  rfl

/-- If all entries are differentiable, `deriv` is computed entrywise. -/
theorem deriv_eq_entrywise [Fintype m] [Fintype n]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : 𝕜 → Matrix m n E} {t : 𝕜}
    (hM : ∀ i j, DifferentiableAt 𝕜 (fun s => M s i j) t) :
    deriv M t = fun i j => deriv (fun s => M s i j) t := by
  have hd : HasDerivAt M (fun i j => deriv (fun s => M s i j) t) t :=
    hasDerivAt_iff_entrywise.mpr (fun i j => (hM i j).hasDerivAt)
  open scoped Matrix.Norms.Elementwise in
    simpa using! hd.deriv

/-- An affine matrix-valued function has its coefficient matrix as derivative. -/
theorem hasDerivAt_affine (X Z : Matrix n n 𝕜) (t : 𝕜) :
    HasDerivAt (fun s : 𝕜 => s • X + Z) X t := by
  apply hasDerivAt_iff_entrywise.mpr
  intro i j
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (X i j)).add_const (Z i j)

end SympyProofs.MatrixDerivative
