module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Limit

/-!
# The limit matrix

This file is about matrices only. `Matrix.Limit` proves that the transition matrices of
a generator converge as time grows. `limitMatrix Q` is a name for that limit. Its entry
at `i j` is the long-run probability of being in state `j` for a chain that starts in
state `i`.

`limitMatrix Q` is defined for every matrix, as a limit that may not exist. Every
statement about it assumes that `Q` is a generator, and then the limit exists, by
`tendsto_transition_limitMatrix`.

* It holds the limit for every start: the row `p ᵥ* transition Q t` tends to
  `p ᵥ* limitMatrix Q`, by `tendsto_vecMul_transition_limitMatrix`.
* Waiting first or afterwards changes nothing: `transition_mul_limitMatrix` and
  `limitMatrix_mul_transition`. So the limit matrix times itself is itself, which is
  `limitMatrix_mul_limitMatrix`.
* `mul_limitMatrix` says `Q * limitMatrix Q = 0`: every column is a conserved quantity.
  `limitMatrix_mul` says `limitMatrix Q * Q = 0`: every row solves the balance equation.
* It is row stochastic, and each of its rows is a stationary distribution, by
  `limitMatrix_mem_rowStochastic` and `isStationaryDistribution_limitMatrix`.
* A row that solves the balance equation is unchanged by it, by
  `vecMul_limitMatrix_of_balance`.
* When some state can be reached from every state, all of its rows are the one
  stationary distribution, by `limitMatrix_row_of_reachable`.

`Matrix.LimitEquation` shows how to compute it by solving a linear system.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix Filter Topology
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The limit of the transition matrices of `Q` as time grows. For a generator the limit
exists, by `tendsto_transition_limitMatrix`. -/
noncomputable def limitMatrix (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  limUnder atTop fun t : ℝ => transition Q t

/-! ### It is the limit -/

/-- The transition matrices of a generator converge to the limit matrix. -/
theorem tendsto_transition_limitMatrix (hQ : IsGenerator Q) :
    Tendsto (fun t : ℝ => transition Q t) atTop (𝓝 (limitMatrix Q)) :=
  tendsto_nhds_limUnder (exists_tendsto_transition hQ)

/-- A matrix that the transition matrices converge to is the limit matrix. -/
theorem eq_limitMatrix_of_tendsto {L : Matrix ι ι ℝ}
    (h : Tendsto (fun t : ℝ => transition Q t) atTop (𝓝 L)) : L = limitMatrix Q :=
  h.limUnder_eq.symm

/-- From every starting row `p`, the row `p ᵥ* transition Q t` converges to `p` times the
limit matrix. -/
theorem tendsto_vecMul_transition_limitMatrix (hQ : IsGenerator Q) (p : ι → ℝ) :
    Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 (p ᵥ* limitMatrix Q)) :=
  ((continuous_const.matrix_vecMul continuous_id).tendsto _).comp
    (tendsto_transition_limitMatrix hQ)

/-! ### Products with transition matrices and with itself -/

/-- Waiting first does not change the long run. -/
theorem transition_mul_limitMatrix (hQ : IsGenerator Q) (s : ℝ) :
    transition Q s * limitMatrix Q = limitMatrix Q := by
  have hL := tendsto_transition_limitMatrix hQ
  have h1 : Tendsto (fun t : ℝ => transition Q s * transition Q t) atTop
      (𝓝 (transition Q s * limitMatrix Q)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hL
  have h2 : Tendsto (fun t : ℝ => transition Q s * transition Q t) atTop
      (𝓝 (limitMatrix Q)) := by
    simp_rw [← transition_add]
    exact hL.comp (tendsto_atTop_add_const_left atTop s tendsto_id)
  exact tendsto_nhds_unique h1 h2

/-- Waiting afterwards does not change the long run. -/
theorem limitMatrix_mul_transition (hQ : IsGenerator Q) (s : ℝ) :
    limitMatrix Q * transition Q s = limitMatrix Q := by
  have hL := tendsto_transition_limitMatrix hQ
  have h1 : Tendsto (fun t : ℝ => transition Q t * transition Q s) atTop
      (𝓝 (limitMatrix Q * transition Q s)) :=
    ((continuous_id.matrix_mul continuous_const).tendsto _).comp hL
  have h2 : Tendsto (fun t : ℝ => transition Q t * transition Q s) atTop
      (𝓝 (limitMatrix Q)) := by
    simp_rw [← transition_add]
    exact hL.comp (tendsto_atTop_add_const_right atTop s tendsto_id)
  exact tendsto_nhds_unique h1 h2

/-- The limit matrix times itself is itself. -/
theorem limitMatrix_mul_limitMatrix (hQ : IsGenerator Q) :
    limitMatrix Q * limitMatrix Q = limitMatrix Q := by
  have h1 : Tendsto (fun t : ℝ => limitMatrix Q * transition Q t) atTop
      (𝓝 (limitMatrix Q * limitMatrix Q)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp
      (tendsto_transition_limitMatrix hQ)
  simp_rw [limitMatrix_mul_transition hQ] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-! ### Products with the generator -/

/-- Every row of the limit matrix solves the balance equation. -/
theorem limitMatrix_mul (hQ : IsGenerator Q) : limitMatrix Q * Q = 0 := by
  ext i j
  have hinv : IsInvariant Q (limitMatrix Q i) := fun s _ =>
    congrFun (limitMatrix_mul_transition hQ s) i
  have hb : limitMatrix Q i ᵥ* Q = 0 := hinv.balance
  exact congrFun hb j

/-- Every column of the limit matrix is annihilated by the generator. -/
theorem mul_limitMatrix (hQ : IsGenerator Q) : Q * limitMatrix Q = 0 := by
  ext i j
  have hinv : IsInvariant Qᵀ (fun k => limitMatrix Q k j) := fun s _ => by
    have ht : transition Qᵀ s = (transition Q s)ᵀ := by
      simp only [transition, ← transpose_smul, MatrixExponential.exp_transpose]
    rw [ht, vecMul_transpose]
    ext k
    exact congrFun (congrFun (transition_mul_limitMatrix hQ s) k) j
  have hb : (fun k => limitMatrix Q k j) ᵥ* Qᵀ = 0 := hinv.balance
  rw [vecMul_transpose] at hb
  exact congrFun hb i

/-- From every starting row, the limit solves the balance equation. -/
theorem balance_vecMul_limitMatrix (hQ : IsGenerator Q) (p : ι → ℝ) :
    Balance Q (p ᵥ* limitMatrix Q) := by
  change (p ᵥ* limitMatrix Q) ᵥ* Q = 0
  rw [vecMul_vecMul, limitMatrix_mul hQ, vecMul_zero]

/-- A row that solves the balance equation is its own limit. -/
theorem vecMul_limitMatrix_of_balance (hQ : IsGenerator Q) {u : ι → ℝ}
    (hu : Balance Q u) : u ᵥ* limitMatrix Q = u :=
  tendsto_nhds_unique (tendsto_vecMul_transition_limitMatrix hQ u)
    (tendsto_const_nhds.congr fun t => (vecMul_transition_of_vecMul_eq_zero hu t).symm)

/-! ### Its rows -/

/-- The limit matrix is row stochastic. -/
theorem limitMatrix_mem_rowStochastic (hQ : IsGenerator Q) :
    limitMatrix Q ∈ Matrix.rowStochastic ℝ ι := by
  have hL := tendsto_transition_limitMatrix hQ
  refine ⟨fun i j => ?_, ?_⟩
  · exact ge_of_tendsto (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hL i) j)
      (eventually_atTop.2 ⟨0, fun t ht => (hQ.transition_mem_rowStochastic t ht).1 i j⟩)
  · have h1 : Tendsto (fun t : ℝ => transition Q t *ᵥ (1 : ι → ℝ)) atTop
        (𝓝 (limitMatrix Q *ᵥ 1)) :=
      ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hL
    simp_rw [transition_mulVec_one Q hQ.mulVec_one_eq_zero] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- Each row of the limit matrix is a stationary distribution. -/
theorem isStationaryDistribution_limitMatrix (hQ : IsGenerator Q) (i : ι) :
    IsStationaryDistribution Q (limitMatrix Q i) :=
  ⟨(limitMatrix_mem_rowStochastic hQ).1 i,
    Matrix.sum_row_of_mem_rowStochastic (limitMatrix_mem_rowStochastic hQ) i,
    congrFun (limitMatrix_mul hQ) i⟩

/-- If some state can be reached from every state, every row of the limit matrix is the
stationary distribution. -/
theorem limitMatrix_row_of_reachable (hQ : IsGenerator Q) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) {w : ι → ℝ} (hw : IsStationaryDistribution Q w) (i : ι) :
    limitMatrix Q i = w := by
  have h1 := tendsto_vecMul_transition_limitMatrix hQ (Pi.single i 1)
  rw [single_one_vecMul] at h1
  exact tendsto_nhds_unique h1 (hw.tendsto_vecMul_transition hQ h (by simp))

end SympyProofs.FiniteMarkovChain
