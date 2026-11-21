module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.LimitMatrix

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The equations that the limit solves

This file is about matrices only. `Convergence` proves that the row
`p ᵥ* transition Q t` converges as time grows, for every generator `Q` and every row
`p`, and `LimitMatrix` names the limit `p ᵥ* limitMatrix Q`. This file says which
linear equations the limit solves, so that it can be computed with no limit and no
matrix exponential.

There are two forms, and each one determines the limit `w`.

* `tendsto_vecMul_transition_iff_forall_dotProduct`: `w` solves the balance equation
  `w ᵥ* Q = 0`, and `w ⬝ᵥ h = p ⬝ᵥ h` for every column `h` with `Q *ᵥ h = 0`.
* `tendsto_vecMul_transition_iff_exists`: `w = p + y ᵥ* Q`, where `y` is any solution of
  `y ᵥ* (Q * Q) = -(p ᵥ* Q)`. Such a `y` always exists.

In the first form, a column `h` with `Q *ᵥ h = 0` is a conserved quantity: the
transition matrices do not change it, by `transition_mulVec_of_mulVec_eq_zero`. So the
limit gives it the same value as the start. The column of all ones is always such a
column, and for it the equation says that `w` has the same total mass as `p`. When some
state can be reached from every state there is no other one, and the system is the
balance equation with total mass one. Otherwise each further independent column adds
one equation, and these fix the solution.

`tendsto_transition_iff_exists` is the second form for all rows at once: the transition
matrices converge to `1 + Y * Q`, where `Y` is any solution of `Y * (Q * Q) = -Q`. So
the limit matrix is `1 + Y * Q` for every such `Y`, and one exists, by
`limitMatrix_eq_of_mul_eq` and `exists_limitMatrix_eq`.

The proof of the first form uses the limit matrix. The limit of a row is stationary
and keeps every conserved quantity, by `vecMul_limitMatrix_dotProduct`. Conversely, a
stationary row is its own limit, and every column of the limit matrix is conserved. So a
stationary row that gives zero on every conserved column is zero. The second form
follows because a row that gives zero on every conserved column is of the form
`y ᵥ* Q`, which is
`exists_eq_vecMul_of_forall_dotProduct_eq_zero`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix Filter Topology
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-! ### Conserved columns -/

/-- A column annihilated by `Q` is unchanged by every transition matrix. -/
theorem transition_mulVec_of_mulVec_eq_zero {h : ι → ℝ} (hh : Q *ᵥ h = 0) (t : ℝ) :
    transition Q t *ᵥ h = h := by
  have hb : h ᵥ* Qᵀ = 0 := by simpa [vecMul_transpose] using hh
  have ht : transition Qᵀ t = (transition Q t)ᵀ := by
    simp only [transition, ← transpose_smul, MatrixExponential.exp_transpose]
  simpa only [ht, vecMul_transpose] using vecMul_transition_of_vecMul_eq_zero hb t

/-- A row that gives zero on every column annihilated by `Q` is of the form `y ᵥ* Q`. -/
theorem exists_eq_vecMul_of_forall_dotProduct_eq_zero (Q : Matrix ι ι ℝ) {x : ι → ℝ}
    (hx : ∀ h : ι → ℝ, Q *ᵥ h = 0 → x ⬝ᵥ h = 0) : ∃ y : ι → ℝ, x = y ᵥ* Q := by
  have hmem : x ∈ LinearMap.range (Matrix.mulVecLin Qᵀ) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    -- every linear functional is a dot product with a column
    have hφx : ∀ z : ι → ℝ, φ z = z ⬝ᵥ fun i => φ (fun j => if i = j then 1 else 0) :=
      fun z => by
        rw [LinearMap.pi_apply_eq_sum_univ φ z]
        simp [dotProduct]
    have hQh : Q *ᵥ (fun i => φ (fun j => if i = j then 1 else 0)) = 0 := by
      ext i
      have h0 := (Submodule.mem_dualAnnihilator φ).1 hφ (Qᵀ *ᵥ Pi.single i 1)
        ⟨Pi.single i 1, rfl⟩
      rw [hφx, mulVec_transpose, ← dotProduct_mulVec, single_one_dotProduct] at h0
      simpa using h0
    rw [hφx, hx _ hQh]
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, by rw [← hy, Matrix.mulVecLin_apply, mulVec_transpose]⟩

/-- From every starting row, the limit gives every column annihilated by `Q` the same
value as the start does. -/
theorem vecMul_limitMatrix_dotProduct (hQ : IsGenerator Q) (p : ι → ℝ) {h : ι → ℝ}
    (hh : Q *ᵥ h = 0) : (p ᵥ* limitMatrix Q) ⬝ᵥ h = p ⬝ᵥ h := by
  have h1 : Tendsto (fun t : ℝ => (p ᵥ* transition Q t) ⬝ᵥ h) atTop
      (𝓝 ((p ᵥ* limitMatrix Q) ⬝ᵥ h)) :=
    ((continuous_id.dotProduct continuous_const).tendsto _).comp
      (tendsto_vecMul_transition_limitMatrix hQ p)
  have h2 : ∀ t : ℝ, (p ᵥ* transition Q t) ⬝ᵥ h = p ⬝ᵥ h := fun t => by
    rw [← dotProduct_mulVec, transition_mulVec_of_mulVec_eq_zero hh]
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-! ### The equations of the limit -/

/-- The limit of the row `p ᵥ* transition Q t` is the one solution `w` of the balance
equation that gives every column annihilated by `Q` the same value as `p` does. -/
theorem tendsto_vecMul_transition_iff_forall_dotProduct (hQ : IsGenerator Q)
    (p w : ι → ℝ) :
    Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) ↔
      Balance Q w ∧ ∀ h : ι → ℝ, Q *ᵥ h = 0 → w ⬝ᵥ h = p ⬝ᵥ h := by
  -- every column of the limit matrix is conserved
  have hcol : ∀ j : ι, Q *ᵥ (fun i => limitMatrix Q i j) = 0 := fun j =>
    funext fun i => congrFun (congrFun (mul_limitMatrix hQ) i) j
  constructor
  · intro hw
    obtain rfl := tendsto_nhds_unique hw (tendsto_vecMul_transition_limitMatrix hQ p)
    exact ⟨balance_vecMul_limitMatrix hQ p,
      fun h hh => vecMul_limitMatrix_dotProduct hQ p hh⟩
  · rintro ⟨hw, hc⟩
    have hu : Balance Q (w - p ᵥ* limitMatrix Q) := by
      have h1 : w ᵥ* Q = 0 := hw
      have h2 : (p ᵥ* limitMatrix Q) ᵥ* Q = 0 := balance_vecMul_limitMatrix hQ p
      change (w - p ᵥ* limitMatrix Q) ᵥ* Q = 0
      rw [sub_vecMul, h1, h2, sub_zero]
    have hzero : w - p ᵥ* limitMatrix Q = 0 := by
      rw [← vecMul_limitMatrix_of_balance hQ hu]
      ext j
      change (w - p ᵥ* limitMatrix Q) ⬝ᵥ (fun i => limitMatrix Q i j) = 0
      rw [sub_dotProduct, hc _ (hcol j), vecMul_limitMatrix_dotProduct hQ p (hcol j),
        sub_self]
    rw [sub_eq_zero.1 hzero]
    exact tendsto_vecMul_transition_limitMatrix hQ p

/-- The limit of the row `p ᵥ* transition Q t` is `p + y ᵥ* Q`, where `y` is any solution
of `y ᵥ* (Q * Q) = -(p ᵥ* Q)`. A solution always exists. -/
theorem tendsto_vecMul_transition_iff_exists (hQ : IsGenerator Q) (p w : ι → ℝ) :
    Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) ↔
      ∃ y : ι → ℝ, y ᵥ* (Q * Q) = -(p ᵥ* Q) ∧ w = p + y ᵥ* Q := by
  rw [tendsto_vecMul_transition_iff_forall_dotProduct hQ]
  constructor
  · rintro ⟨hw, hc⟩
    obtain ⟨y, hy⟩ := exists_eq_vecMul_of_forall_dotProduct_eq_zero Q (x := w - p)
      fun h hh => by rw [sub_dotProduct, hc h hh, sub_self]
    have h1 : w ᵥ* Q = 0 := hw
    refine ⟨y, ?_, by rw [← hy, add_sub_cancel]⟩
    rw [← vecMul_vecMul, ← hy, sub_vecMul, h1, zero_sub]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun h hh => ?_⟩
    · change (p + y ᵥ* Q) ᵥ* Q = 0
      rw [add_vecMul, vecMul_vecMul, hy, add_neg_cancel]
    · rw [add_dotProduct, ← dotProduct_mulVec, hh, dotProduct_zero, add_zero]

/-- The transition matrices converge to `1 + Y * Q`, where `Y` is any solution of
`Y * (Q * Q) = -Q`. A solution always exists. -/
theorem tendsto_transition_iff_exists (hQ : IsGenerator Q) (L : Matrix ι ι ℝ) :
    Tendsto (fun t : ℝ => transition Q t) atTop (𝓝 L) ↔
      ∃ Y : Matrix ι ι ℝ, Y * (Q * Q) = -Q ∧ L = 1 + Y * Q := by
  have hone : ∀ i j : ι, (Pi.single i 1 : ι → ℝ) j = (1 : Matrix ι ι ℝ) i j := fun i j => by
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hrow : Tendsto (fun t : ℝ => transition Q t) atTop (𝓝 L) ↔
      ∀ i, Tendsto (fun t : ℝ => Pi.single i 1 ᵥ* transition Q t) atTop (𝓝 (L i)) := by
    simp only [single_one_vecMul]
    exact tendsto_pi_nhds
  rw [hrow]
  simp_rw [tendsto_vecMul_transition_iff_exists hQ]
  constructor
  · intro h
    choose Y hY1 hY2 using h
    refine ⟨Y, ?_, ?_⟩
    · ext i j
      have h1 := congrFun (hY1 i) j
      rw [single_one_vecMul] at h1
      exact h1
    · ext i j
      rw [hY2 i, Pi.add_apply, hone]
      rfl
  · rintro ⟨Y, hY, rfl⟩ i
    refine ⟨Y i, ?_, ?_⟩
    · rw [single_one_vecMul]
      exact congrFun hY i
    · ext j
      rw [Pi.add_apply, hone]
      rfl

/-- The limit matrix is `1 + Y * Q` for some solution `Y` of `Y * (Q * Q) = -Q`. -/
theorem exists_limitMatrix_eq (hQ : IsGenerator Q) :
    ∃ Y : Matrix ι ι ℝ, Y * (Q * Q) = -Q ∧ limitMatrix Q = 1 + Y * Q :=
  (tendsto_transition_iff_exists hQ _).1 (tendsto_transition_limitMatrix hQ)

/-- The limit matrix is `1 + Y * Q` for every solution `Y` of `Y * (Q * Q) = -Q`. -/
theorem limitMatrix_eq_of_mul_eq (hQ : IsGenerator Q) {Y : Matrix ι ι ℝ}
    (hY : Y * (Q * Q) = -Q) : limitMatrix Q = 1 + Y * Q :=
  (eq_limitMatrix_of_tendsto ((tendsto_transition_iff_exists hQ _).2 ⟨Y, hY, rfl⟩)).symm

end SympyProofs.FiniteMarkovChain
