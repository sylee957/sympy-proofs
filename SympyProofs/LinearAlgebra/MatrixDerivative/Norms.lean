module

public import SympyProofs.LinearAlgebra.MatrixDerivative.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.Matrix.Normed

import Mathlib.Analysis.Normed.Order.Hom.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Independence of the scalar matrix derivative from the matrix norm.

An arbitrary vector-space norm is represented by a function-like `p : F`, with
`SeminormClass` supplying scalar homogeneity and `AddGroupNormClass` supplying
definiteness. Finite dimensionality ensures its topology is the usual matrix
topology. No continuity assumption on `p`, submultiplicativity, or normalization
at the identity matrix is required.

The entrywise maximum, Frobenius, and maximum row-sum operator norms are provided
as definite seminorms with both class instances, so they can be used directly in
the derivative and differentiability criteria below.
-/

@[expose] public section

namespace SympyProofs.MatrixDerivative

open Filter
open scoped NNReal Topology

/-- Seminorms with trivial kernel, using the same underlying function for both
the seminorm and additive group norm interfaces. -/
abbrev DefiniteSeminorm (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] :=
  {p : Seminorm 𝕜 E // ∀ x, p x = 0 → x = 0}

namespace DefiniteSeminorm

instance instFunLike {𝕜 E : Type*} [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] :
    FunLike (DefiniteSeminorm 𝕜 E) E ℝ where
  coe p := p.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

instance instSeminormClass {𝕜 E : Type*} [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] :
    SeminormClass (DefiniteSeminorm 𝕜 E) 𝕜 E where
  map_zero p := map_zero p.val
  map_add_le_add p := map_add_le_add p.val
  map_neg_eq_map p := map_neg_eq_map p.val
  map_smul_eq_mul p := map_smul_eq_mul p.val

instance instAddGroupNormClass {𝕜 E : Type*} [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] :
    AddGroupNormClass (DefiniteSeminorm 𝕜 E) E ℝ where
  toAddGroupSeminormClass := inferInstance
  eq_zero_of_map_eq_zero p := p.property _

/-- The chosen norm of a normed vector space, bundled as a definite seminorm. -/
def ofNorm (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    DefiniteSeminorm 𝕜 E :=
  ⟨normSeminorm 𝕜 E, fun _ h => norm_eq_zero.mp h⟩

@[simp]
theorem ofNorm_apply {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) : ofNorm 𝕜 E x = ‖x‖ := rfl

end DefiniteSeminorm

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
variable {M : 𝕜 → Matrix m n 𝕜} {D : Matrix m n 𝕜} {t : 𝕜}

open scoped Matrix.Norms.Elementwise in
/-- The maximum of the norms of the entries, with value zero for empty matrices. -/
noncomputable def entrywiseNorm : DefiniteSeminorm 𝕜 (Matrix m n 𝕜) :=
  DefiniteSeminorm.ofNorm 𝕜 (Matrix m n 𝕜)

open scoped Matrix.Norms.Frobenius in
/-- The square root of the sum of squared entry norms. -/
noncomputable def frobeniusNorm : DefiniteSeminorm 𝕜 (Matrix m n 𝕜) :=
  DefiniteSeminorm.ofNorm 𝕜 (Matrix m n 𝕜)

open scoped Matrix.Norms.Operator in
/-- The operator norm induced by the vector sup norm: the maximum absolute row sum. -/
noncomputable def linftyOperatorNorm : DefiniteSeminorm 𝕜 (Matrix m n 𝕜) :=
  DefiniteSeminorm.ofNorm 𝕜 (Matrix m n 𝕜)

theorem entrywiseNorm_apply (A : Matrix m n 𝕜) :
    entrywiseNorm A =
      ((Finset.univ.sup fun i => Finset.univ.sup fun j => ‖A i j‖₊ : ℝ≥0) : ℝ) := by
  open scoped Matrix.Norms.Elementwise in
    exact Matrix.norm_eq_sup_sup_nnnorm A

theorem frobeniusNorm_apply (A : Matrix m n 𝕜) :
    frobeniusNorm A = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  open scoped Matrix.Norms.Frobenius in
    simpa only [frobeniusNorm, DefiniteSeminorm.ofNorm_apply, Real.sqrt_eq_rpow,
      Real.rpow_two] using Matrix.frobenius_norm_def A

theorem linftyOperatorNorm_apply (A : Matrix m n 𝕜) :
    linftyOperatorNorm A = ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : ℝ≥0) : ℝ) := by
  open scoped Matrix.Norms.Operator in
    exact Matrix.linfty_opNorm_def A

/-- The first-order remainder criterion in any vector-space norm on finite
matrices is equivalent to `HasDerivAt` in the usual matrix topology. -/
theorem hasDerivAt_iff_tendsto_norm {F : Type*} [FunLike F (Matrix m n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass F (Matrix m n 𝕜) ℝ]
    (p : F) :
    HasDerivAt M D t ↔
      Tendsto (fun s => p (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0) := by
  let : IsModuleTopology 𝕜 (Matrix m n 𝕜) := isModuleTopologyOfFiniteDimensional
  have hstd := eq_moduleTopology 𝕜 (Matrix m n 𝕜)
  let N := AddGroupNormClass.toNormedAddCommGroup p
  let : NormedAddCommGroup (Matrix m n 𝕜) := N
  let : NormedSpace 𝕜 (Matrix m n 𝕜) :=
    { norm_smul_le := fun c A => (map_smul_eq_mul p c A).le }
  let : TopologicalSpace (Matrix m n 𝕜) := N.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : IsModuleTopology 𝕜 (Matrix m n 𝕜) := isModuleTopologyOfFiniteDimensional
  have htop := (eq_moduleTopology 𝕜 (Matrix m n 𝕜)).trans hstd.symm
  have h := hasDerivAt_iff_tendsto (f := M) (f' := D) (x := t)
  simp only [div_eq_mul_inv, mul_comm]
  convert! h using 2
  exact htop.symm

/-- The norm remainder criterion is equivalent to differentiating every entry. -/
theorem tendsto_norm_iff_entrywise {F : Type*} [FunLike F (Matrix m n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass F (Matrix m n 𝕜) ℝ]
    (p : F) :
    Tendsto (fun s => p (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0) ↔
      ∀ i j, HasDerivAt (fun s => M s i j) (D i j) t :=
  (hasDerivAt_iff_tendsto_norm p).symm.trans hasDerivAt_iff_entrywise

/-- A matrix-valued function is differentiable exactly when some matrix satisfies
the first-order remainder criterion in the chosen vector-space norm. -/
theorem differentiableAt_iff_exists_tendsto_norm {F : Type*}
    [FunLike F (Matrix m n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass F (Matrix m n 𝕜) ℝ]
    (p : F) :
    DifferentiableAt 𝕜 M t ↔ ∃ D : Matrix m n 𝕜,
      Tendsto (fun s => p (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L 1, (hasDerivAt_iff_tendsto_norm p).mp hL.hasDerivAt⟩
  · rintro ⟨D, hD⟩
    exact ⟨_, ((hasDerivAt_iff_tendsto_norm p).mpr hD).hasFDerivAt⟩

/-- Changing the matrix norm does not change the first-order remainder criterion. -/
theorem tendsto_norm_iff {F G : Type*}
    [FunLike F (Matrix m n 𝕜) ℝ] [FunLike G (Matrix m n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass F (Matrix m n 𝕜) ℝ]
    [SeminormClass G 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass G (Matrix m n 𝕜) ℝ]
    (p : F) (q : G) :
    Tendsto (fun s => p (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0) ↔
      Tendsto (fun s => q (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0) :=
  (hasDerivAt_iff_tendsto_norm p).symm.trans (hasDerivAt_iff_tendsto_norm q)

/-- Existence of a matrix derivative in the remainder-limit sense is independent
of the vector-space norm. -/
theorem exists_tendsto_norm_iff {F G : Type*}
    [FunLike F (Matrix m n 𝕜) ℝ] [FunLike G (Matrix m n 𝕜) ℝ]
    [SeminormClass F 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass F (Matrix m n 𝕜) ℝ]
    [SeminormClass G 𝕜 (Matrix m n 𝕜)] [AddGroupNormClass G (Matrix m n 𝕜) ℝ]
    (p : F) (q : G) :
    (∃ D : Matrix m n 𝕜,
      Tendsto (fun s => p (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0)) ↔
    (∃ D : Matrix m n 𝕜,
      Tendsto (fun s => q (M s - M t - (s - t) • D) / ‖s - t‖) (𝓝 t) (𝓝 0)) :=
  exists_congr fun _ => tendsto_norm_iff p q

end SympyProofs.MatrixDerivative
