module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.MatrixStationary
public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Reachable

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence to the stationary distribution

This file is about matrices only. Start a chain with generator `Q` from a row `p`. Its
distribution at time `t` is `p ᵥ* transition Q t`.

Suppose some state `j₀` can be reached from every state, that is, `Reachable Q i j₀`
for every `i`. Then three things hold.

* A stationary distribution exists, by `exists_isStationaryDistribution`.
* The balance equation has only one solution of total mass one, by
  `Balance.eq_of_sum_eq_one`. No sign condition is needed for this.
* The distribution converges to the stationary distribution from every start, by
  `IsStationaryDistribution.tendsto_vecMul_transition`.

All three come from one argument. By `exists_transition_pos_of_reachable` there is one
positive time `t₀` with `0 < transition Q t₀ i j₀` for every `i`. The argument measures
the distance between two rows by the sum
of the absolute values of the differences of their entries. Every row-stochastic matrix
does not increase that distance. One whose column `j₀` is at least `ε` shrinks it by
the factor `1 - ε` for rows of equal total mass. So the distributions at the multiples
of `t₀` form a Cauchy sequence, its limit does not depend on the start, and the times
in between are controlled by the first fact.

The condition cannot be dropped. A chain with two states that are never left keeps
whichever one it starts in.

In fact the condition is necessary for uniqueness: if a generator has at most one
stationary distribution, some state can be reached from every state. This is
`exists_reachable_of_isStationaryDistribution_unique`. So a generator has exactly one
stationary distribution exactly when some state can be reached from every state, which
is `existsUnique_isStationaryDistribution_iff`.

The proof of the converse goes as follows. From every state one can reach a state `a`
that can be reached back from every state reachable from `a`. For such an `a` there is
a stationary distribution that is zero outside the states reachable from `a`, by
`exists_isStationaryDistribution_eq_zero_of_not_reachable`. To get it, change the
generator so that every state not reachable from `a` moves to `a` at rate `1`. Then `a`
can be reached from every state, so the first fact above gives a stationary
distribution of the changed generator. It has no mass on the changed rows, so it is a
stationary distribution of the original generator too. Now take such an `a` and, for
any state `i`, such an `a'` reachable from `i`. If there is only one stationary
distribution, the two distributions agree, so some state is reachable from both `a` and
`a'`. From there the chain can go back to `a`. So `a` can be reached from `i`.

Without the condition the transition matrices still converge as time grows. This is
`exists_tendsto_transition`. So from every starting distribution the distribution
converges to a stationary distribution, by `exists_isStationaryDistribution_tendsto`.
The limit may depend on the start. In particular a generator on at least one state
always has a stationary distribution.

The proof has three steps. Call a state returning if it can be reached back from every
state reachable from it. First, the row of a returning state converges: the changed
generator above has the same transitions from that state, and the first part of this
file applies to it. Second, from every state the probability of being at a state that
is not returning becomes as small as one likes. It is below `1` from every state at one
common time, so it is at most a factor `c < 1` there, and the factor applies again with
every further step of that length. Third, split a long time into a first part, after
which almost all mass is on returning states, and a rest, over which the rows of the
returning states are close to their limits. This shows that every entry is a Cauchy
function of time.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix Filter Topology
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι]

/-- The sum of the absolute values of the entries of a row. -/
private def rowNorm (x : ι → ℝ) : ℝ := ∑ i, |x i|

private theorem rowNorm_nonneg (x : ι → ℝ) : 0 ≤ rowNorm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem abs_le_rowNorm (x : ι → ℝ) (j : ι) : |x j| ≤ rowNorm x :=
  Finset.single_le_sum (f := fun i => |x i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- Multiplying a row by a nonnegative matrix with constant row sums `c` multiplies
its norm by at most `c`. -/
private theorem rowNorm_vecMul_le {N : Matrix ι ι ℝ} (hN : ∀ i j, 0 ≤ N i j) {c : ℝ}
    (hc : ∀ i, ∑ j, N i j = c) (x : ι → ℝ) : rowNorm (x ᵥ* N) ≤ c * rowNorm x := by
  simp only [rowNorm, Matrix.vecMul, dotProduct]
  calc ∑ j, |∑ i, x i * N i j| ≤ ∑ j, ∑ i, |x i| * N i j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hN i j)]
    _ = ∑ i, |x i| * ∑ j, N i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = c * ∑ i, |x i| := by
        simp_rw [hc]
        rw [← Finset.sum_mul, mul_comm]

variable [DecidableEq ι]

/-- A row-stochastic matrix whose column `j₀` is at least `ε` brings rows of equal
total mass closer by the factor `1 - ε`. -/
private theorem rowNorm_vecMul_le_of_column {M : Matrix ι ι ℝ}
    (hM : M ∈ Matrix.rowStochastic ℝ ι)
    {ε : ℝ} {j₀ : ι} (hε : ∀ i, ε ≤ M i j₀) {x : ι → ℝ} (hx : ∑ i, x i = 0) :
    rowNorm (x ᵥ* M) ≤ (1 - ε) * rowNorm x := by
  let N : Matrix ι ι ℝ := fun i j => M i j - if j = j₀ then ε else 0
  have hN : ∀ i j, 0 ≤ N i j := by
    intro i j
    by_cases hj : j = j₀
    · subst hj
      simpa [N] using hε i
    · simpa [N, hj] using hM.1 i j
  have hc : ∀ i, ∑ j, N i j = 1 - ε := by
    intro i
    simp only [N, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Matrix.sum_row_of_mem_rowStochastic hM i]
  have hxN : x ᵥ* M = x ᵥ* N := by
    ext j
    simp only [Matrix.vecMul, dotProduct, N, mul_sub, Finset.sum_sub_distrib]
    have h0 : ∑ i, x i * (if j = j₀ then ε else 0) = 0 := by
      rw [← Finset.sum_mul, hx, zero_mul]
    rw [h0, sub_zero]
  rw [hxN]
  exact rowNorm_vecMul_le hN hc x

/-- If some state can be reached from every state in time `t₀`, the chain forgets its
start: there is one row `w` to which the distribution converges from every start. It
is the only row of total mass one that satisfies the balance equation. -/
private theorem exists_limit_row {Q : Matrix ι ι ℝ} (hQ : IsGenerator Q) {t₀ : ℝ}
    (ht₀ : 0 < t₀) {j₀ : ι} (h : ∀ i, 0 < transition Q t₀ i j₀) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ Balance Q w ∧
      (∀ v : ι → ℝ, ∑ i, v i = 1 → Balance Q v → v = w) ∧
      ∀ p : ι → ℝ, ∑ i, p i = 1 →
        Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) := by
  have hM : transition Q t₀ ∈ Matrix.rowStochastic ℝ ι :=
    hQ.transition_mem_rowStochastic t₀ ht₀.le
  -- a uniform lower bound for the column `j₀`
  obtain ⟨ε, hε0, hε1, hεle⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ i, ε ≤ transition Q t₀ i j₀ := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
      (fun i => transition Q t₀ i j₀) ⟨j₀, Finset.mem_univ _⟩
    refine ⟨transition Q t₀ i₀ j₀, h i₀, ?_, fun i => hi₀ i (Finset.mem_univ i)⟩
    have hle := Finset.single_le_sum (f := fun j => transition Q t₀ i₀ j)
      (fun j _ => hM.1 i₀ j) (Finset.mem_univ j₀)
    rwa [Matrix.sum_row_of_mem_rowStochastic hM i₀] at hle
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  -- contraction along the multiples of `t₀`
  have hiter : ∀ x : ι → ℝ, ∑ i, x i = 0 → ∀ n : ℕ,
      rowNorm (x ᵥ* transition Q (n * t₀)) ≤ (1 - ε) ^ n * rowNorm x := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ((n + 1 : ℕ) : ℝ) * t₀ = n * t₀ + t₀ := by push_cast; ring
      rw [e, vecMul_transition_add]
      have hz : ∑ i, (x ᵥ* transition Q (n * t₀)) i = 0 := by
        rw [sum_vecMul_transition hQ, hx]
      calc rowNorm ((x ᵥ* transition Q (n * t₀)) ᵥ* transition Q t₀)
          ≤ (1 - ε) * rowNorm (x ᵥ* transition Q (n * t₀)) :=
            rowNorm_vecMul_le_of_column hM hεle hz
        _ ≤ (1 - ε) * ((1 - ε) ^ n * rowNorm x) := mul_le_mul_of_nonneg_left ih hr0
        _ = (1 - ε) ^ (n + 1) * rowNorm x := by ring
  -- start from a point mass and iterate
  let e : ι → ℝ := Pi.single j₀ 1
  have he1 : ∑ i, e i = 1 := by simp [e]
  have he0 : ∀ i, 0 ≤ e i := fun i => by
    by_cases hi : i = j₀ <;> simp [e, hi]
  let u : ℕ → ι → ℝ := fun n => e ᵥ* transition Q (n * t₀)
  have hstep : ∀ n, u (n + 1) = u n ᵥ* transition Q t₀ := fun n => by
    simp only [u]
    rw [show ((n + 1 : ℕ) : ℝ) * t₀ = n * t₀ + t₀ by push_cast; ring,
      vecMul_transition_add]
  have hsum_u : ∀ n, ∑ i, u n i = 1 := fun n => by
    simp only [u]
    rw [sum_vecMul_transition hQ, he1]
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric (1 - ε) (rowNorm (e - e ᵥ* transition Q t₀)) hr1
      fun n => ?_
    have hdiff : u n - u (n + 1) =
        (e - e ᵥ* transition Q t₀) ᵥ* transition Q (n * t₀) := by
      simp only [u]
      rw [show ((n + 1 : ℕ) : ℝ) * t₀ = t₀ + n * t₀ by push_cast; ring,
        vecMul_transition_add, Matrix.sub_vecMul]
    have hz : ∑ i, (e - e ᵥ* transition Q t₀) i = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [sum_vecMul_transition hQ, sub_self]
    calc dist (u n) (u (n + 1)) ≤ rowNorm (u n - u (n + 1)) := by
          refine (dist_pi_le_iff (rowNorm_nonneg _)).2 fun i => ?_
          rw [Real.dist_eq]
          exact abs_le_rowNorm (u n - u (n + 1)) i
      _ ≤ (1 - ε) ^ n * rowNorm (e - e ᵥ* transition Q t₀) := by
          rw [hdiff]
          exact hiter _ hz n
      _ = rowNorm (e - e ᵥ* transition Q t₀) * (1 - ε) ^ n := mul_comm _ _
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hw0 : ∀ i, 0 ≤ w i := fun i =>
    ge_of_tendsto' (tendsto_pi_nhds.1 hw i) fun n =>
      Matrix.nonneg_vecMul_of_mem_rowStochastic
        (hQ.transition_mem_rowStochastic _ (mul_nonneg (Nat.cast_nonneg n) ht₀.le)) he0 i
  have hw1 : ∑ i, w i = 1 :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun i _ => tendsto_pi_nhds.1 hw i)
      (tendsto_const_nhds.congr fun n => (hsum_u n).symm)
  have hwM : w ᵥ* transition Q t₀ = w := by
    have h1 : Tendsto (fun n => u n ᵥ* transition Q t₀) atTop
        (𝓝 (w ᵥ* transition Q t₀)) :=
      ((continuous_id.matrix_vecMul continuous_const).tendsto w).comp hw
    have h2 : Tendsto (fun n => u n ᵥ* transition Q t₀) atTop (𝓝 w) := by
      simp_rw [← hstep]
      exact hw.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 h2
  -- a row of total mass one that is fixed by the transition over `t₀` is `w`
  have huniq : ∀ v : ι → ℝ, ∑ i, v i = 1 → v ᵥ* transition Q t₀ = v → v = w := by
    intro v hv1 hvM
    have hz : ∑ i, (v - w) i = 0 := by simp [Finset.sum_sub_distrib, hv1, hw1]
    have hfix : (v - w) ᵥ* transition Q t₀ = v - w := by rw [Matrix.sub_vecMul, hvM, hwM]
    have hle := rowNorm_vecMul_le_of_column hM hεle hz
    rw [hfix] at hle
    have hmul : ε * rowNorm (v - w) ≤ ε * 0 := by
      have : (1 - ε) * rowNorm (v - w) = rowNorm (v - w) - ε * rowNorm (v - w) := by ring
      linarith
    have hzero : rowNorm (v - w) ≤ 0 := le_of_mul_le_mul_left hmul hε0
    funext i
    have h0 : v i - w i = 0 := abs_nonpos_iff.1 ((abs_le_rowNorm (v - w) i).trans hzero)
    linarith
  have hinv : ∀ s : ℝ, 0 ≤ s → w ᵥ* transition Q s = w := by
    intro s _
    refine huniq _ (by rw [sum_vecMul_transition hQ, hw1]) ?_
    rw [← vecMul_transition_add, add_comm, vecMul_transition_add, hwM]
  refine ⟨w, hw0, hw1, IsInvariant.balance hinv, fun v hv1 hv =>
    huniq v hv1 (hv.isInvariant t₀ ht₀.le), fun p hp1 => ?_⟩
  -- convergence from an arbitrary start
  have hz : ∑ i, (p - w) i = 0 := by simp [Finset.sum_sub_distrib, hp1, hw1]
  have hbound : ∀ n : ℕ, ∀ t : ℝ, n * t₀ ≤ t →
      rowNorm (p ᵥ* transition Q t - w) ≤ (1 - ε) ^ n * rowNorm (p - w) := by
    intro n t ht
    have hs : 0 ≤ t - n * t₀ := sub_nonneg.2 ht
    have hnt : 0 ≤ (n : ℝ) * t₀ := mul_nonneg (Nat.cast_nonneg n) ht₀.le
    have hsplit : p ᵥ* transition Q t - w =
        ((p - w) ᵥ* transition Q (n * t₀)) ᵥ* transition Q (t - n * t₀) := by
      rw [← vecMul_transition_add, show (n : ℝ) * t₀ + (t - n * t₀) = t by ring,
        Matrix.sub_vecMul, hinv t (hnt.trans ht)]
    have hS := hQ.transition_mem_rowStochastic (t - n * t₀) hs
    rw [hsplit]
    calc rowNorm (((p - w) ᵥ* transition Q (n * t₀)) ᵥ* transition Q (t - n * t₀))
        ≤ 1 * rowNorm ((p - w) ᵥ* transition Q (n * t₀)) :=
          rowNorm_vecMul_le hS.1 (fun i => Matrix.sum_row_of_mem_rowStochastic hS i) _
      _ ≤ (1 - ε) ^ n * rowNorm (p - w) := by
          rw [one_mul]
          exact hiter _ hz n
  refine tendsto_pi_nhds.2 fun j => ?_
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hpos : 0 < rowNorm (p - w) + 1 :=
    add_pos_of_nonneg_of_pos (rowNorm_nonneg (p - w)) one_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hpos) hr1
  refine ⟨n * t₀, fun t ht => ?_⟩
  rw [Real.dist_eq]
  calc |(p ᵥ* transition Q t) j - w j| ≤ rowNorm (p ᵥ* transition Q t - w) :=
        abs_le_rowNorm (p ᵥ* transition Q t - w) j
    _ ≤ (1 - ε) ^ n * rowNorm (p - w) := hbound n t ht
    _ ≤ (1 - ε) ^ n * (rowNorm (p - w) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 n)
    _ < δ := (lt_div_iff₀ hpos).1 hn

variable {Q : Matrix ι ι ℝ} {j₀ : ι}

/-- The same with the time left out of the hypothesis. -/
private theorem exists_limit_row_of_reachable (hQ : IsGenerator Q)
    (h : ∀ i, Reachable Q i j₀) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ Balance Q w ∧
      (∀ v : ι → ℝ, ∑ i, v i = 1 → Balance Q v → v = w) ∧
      ∀ p : ι → ℝ, ∑ i, p i = 1 →
        Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) := by
  obtain ⟨t₀, ht₀, hpos⟩ := exists_transition_pos_of_reachable hQ h
  exact exists_limit_row hQ (show (0 : ℝ) < t₀ from ht₀) hpos

/-- If some state can be reached from every state, a stationary distribution exists. -/
theorem exists_isStationaryDistribution (hQ : IsGenerator Q)
    (h : ∀ i, Reachable Q i j₀) : ∃ w : ι → ℝ, IsStationaryDistribution Q w := by
  obtain ⟨w, h0, h1, hb, -, -⟩ := exists_limit_row_of_reachable hQ h
  exact ⟨w, h0, h1, hb⟩

/-- If some state can be reached from every state, the balance equation has at most one
solution of total mass one. -/
theorem Balance.eq_of_sum_eq_one (hQ : IsGenerator Q) (h : ∀ i, Reachable Q i j₀)
    {v w : ι → ℝ} (hv : Balance Q v) (hw : Balance Q w) (hv1 : ∑ i, v i = 1)
    (hw1 : ∑ i, w i = 1) : v = w := by
  obtain ⟨u, -, -, -, hu, -⟩ := exists_limit_row_of_reachable hQ h
  rw [hu v hv1 hv, hu w hw1 hw]

/-- If some state can be reached from every state, the distribution converges to the
stationary distribution from every start. -/
theorem IsStationaryDistribution.tendsto_vecMul_transition (hQ : IsGenerator Q)
    (h : ∀ i, Reachable Q i j₀) {w : ι → ℝ} (hw : IsStationaryDistribution Q w)
    {p : ι → ℝ} (hp : ∑ i, p i = 1) :
    Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) := by
  obtain ⟨u, -, -, -, hu, hl⟩ := exists_limit_row_of_reachable hQ h
  rw [hu w hw.sum_eq_one hw.balance]
  exact hl p hp

/-! ### The converse of uniqueness -/

/-- Keep the rows of the states reachable from `a` and let every other state move to `a`
at rate `1`. If `a` can be reached back from every state reachable from `a`, the result
is a generator for which `a` can be reached from every state. -/
private theorem exists_generator_eq_of_reachable (hQ : IsGenerator Q) {a : ι}
    (ha : ∀ b, Reachable Q a b → Reachable Q b a) :
    ∃ Q' : Matrix ι ι ℝ, IsGenerator Q' ∧ (∀ i, Reachable Q' i a) ∧
      (∀ i j, Reachable Q a i → Q' i j = Q i j) ∧
      ∀ i j, ¬Reachable Q a i →
        Q' i j = (if j = a then 1 else 0) - (if j = i then 1 else 0) := by
  classical
  obtain ⟨Q', hC, hN⟩ : ∃ Q' : Matrix ι ι ℝ,
      (∀ i j, Reachable Q a i → Q' i j = Q i j) ∧
      ∀ i j, ¬Reachable Q a i →
        Q' i j = (if j = a then 1 else 0) - (if j = i then 1 else 0) :=
    ⟨fun i j => if Reachable Q a i then Q i j
      else (if j = a then 1 else 0) - (if j = i then 1 else 0),
      fun i j h => by simp [h], fun i j h => by simp [h]⟩
  have haa : Reachable Q a a := Reachable.refl Q a
  have hQ' : IsGenerator Q' := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · by_cases hi : Reachable Q a i
      · rw [hC i j hi]
        exact hQ.offDiag_nonneg i j hij
      · have hji : ¬j = i := Ne.symm hij
        rw [hN i j hi]
        simp only [hji, ite_false, sub_zero]
        split_ifs <;> norm_num
    · by_cases hi : Reachable Q a i
      · simp_rw [hC i _ hi]
        exact hQ.row_sum_zero i
      · simp_rw [hN i _ hi]
        simp
  refine ⟨Q', hQ', fun i => ?_, hC, hN⟩
  by_cases hi : Reachable Q a i
  · have key : ∀ c, Relation.ReflTransGen (fun x y => 0 < Q x y) i c →
        Relation.ReflTransGen (fun x y => 0 < Q' x y) i c ∧ Reachable Q a c := by
      intro c hc
      induction hc with
      | refl => exact ⟨Relation.ReflTransGen.refl, hi⟩
      | tail _ hbc ih =>
        exact ⟨ih.1.tail (by rw [hC _ _ ih.2]; exact hbc),
          hQ.reachable_trans ih.2 (hQ.reachable_of_pos hbc)⟩
    exact hQ'.reachable_of_reflTransGen
      (key a (hQ.reflTransGen_of_reachable (ha i hi))).1
  · refine hQ'.reachable_of_pos ?_
    have hai : a ≠ i := fun h => hi (h ▸ haa)
    rw [hN i a hi]
    simp [hai]

/-- If `a` can be reached back from every state reachable from `a`, there is a stationary
distribution that is zero outside the states reachable from `a`. -/
theorem exists_isStationaryDistribution_eq_zero_of_not_reachable (hQ : IsGenerator Q)
    {a : ι} (ha : ∀ b, Reachable Q a b → Reachable Q b a) :
    ∃ w : ι → ℝ, IsStationaryDistribution Q w ∧ ∀ b, ¬Reachable Q a b → w b = 0 := by
  classical
  obtain ⟨Q', hQ', hreach, hC, hN⟩ := exists_generator_eq_of_reachable hQ ha
  have haa : Reachable Q a a := Reachable.refl Q a
  obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ' hreach
  -- The mass outside the states reachable from `a` is zero.
  have hzero : ∀ b, ¬Reachable Q a b → w b = 0 := by
    let x : ι → ℝ := fun j => if Reachable Q a j then 0 else 1
    have hx : Q' *ᵥ x = -x := by
      ext i
      by_cases hi : Reachable Q a i
      · simp only [mulVec, dotProduct, Pi.neg_apply, x, hi, ite_true, neg_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : Reachable Q a j
        · simp [hj]
        · rw [hC i j hi, hQ.eq_zero_of_reachable_of_not_reachable hi hj, zero_mul]
      · simp only [mulVec, dotProduct, Pi.neg_apply]
        simp_rw [hN i _ hi, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp [x, hi, haa]
    have h0 : ∑ i, w i * x i = 0 := by
      have h := dotProduct_mulVec w Q' x
      rw [hx, hw.balance] at h
      simpa [dotProduct] using h
    intro b hb
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ w i * x i := fun i _ =>
      mul_nonneg (hw.nonneg i) (by simp only [x]; split_ifs <;> norm_num)
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h0 b (Finset.mem_univ b)
    simpa [x, hb] using this
  refine ⟨w, ⟨hw.nonneg, hw.sum_eq_one, ?_⟩, hzero⟩
  ext j
  have hj := congrFun hw.balance j
  simp only [vecMul, dotProduct, Pi.zero_apply] at hj ⊢
  rw [← hj]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : Reachable Q a i
  · rw [hC i j hi]
  · rw [hzero i hi, zero_mul, zero_mul]

/-- If a generator has at most one stationary distribution, some state can be reached
from every state. -/
theorem exists_reachable_of_isStationaryDistribution_unique [Nonempty ι]
    (hQ : IsGenerator Q)
    (h : ∀ v w, IsStationaryDistribution Q v → IsStationaryDistribution Q w → v = w) :
    ∃ j₀, ∀ i, Reachable Q i j₀ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨a, -, ha⟩ := hQ.exists_reachable_forall_reachable i₀
  obtain ⟨w, hw, hw0⟩ := exists_isStationaryDistribution_eq_zero_of_not_reachable hQ ha
  refine ⟨a, fun i => ?_⟩
  obtain ⟨a', hia', ha'⟩ := hQ.exists_reachable_forall_reachable i
  obtain ⟨w', hw', hw0'⟩ := exists_isStationaryDistribution_eq_zero_of_not_reachable hQ ha'
  obtain rfl := h w w' hw hw'
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := hw.sum_eq_one
    simp [hall] at h1
  have hab : Reachable Q a b := not_not.1 fun hn => hb (hw0 b hn)
  have ha'b : Reachable Q a' b := not_not.1 fun hn => hb (hw0' b hn)
  exact hQ.reachable_trans hia' (hQ.reachable_trans ha'b (ha b hab))

/-- A generator has exactly one stationary distribution exactly when some state can be
reached from every state. -/
theorem existsUnique_isStationaryDistribution_iff (hQ : IsGenerator Q) :
    (∃! w, IsStationaryDistribution Q w) ↔ ∃ j₀, ∀ i, Reachable Q i j₀ := by
  constructor
  · rintro ⟨w, hw, hu⟩
    have : Nonempty ι := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h1 := hw.sum_eq_one
      simp at h1
    exact exists_reachable_of_isStationaryDistribution_unique hQ
      fun v v' hv hv' => (hu v hv).trans (hu v' hv').symm
  · rintro ⟨j₀, h⟩
    obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ h
    exact ⟨w, hw, fun v hv =>
      Balance.eq_of_sum_eq_one hQ h hv.balance hw.balance hv.sum_eq_one hw.sum_eq_one⟩

/-! ### Convergence without the reachability condition -/

/-- The row of a state that can be reached back from every state it reaches converges. -/
private theorem exists_tendsto_transition_row (hQ : IsGenerator Q) {a : ι}
    (ha : ∀ b, Reachable Q a b → Reachable Q b a) :
    ∃ L : ι → ℝ, Tendsto (fun t : ℝ => transition Q t a) atTop (𝓝 L) := by
  obtain ⟨Q', hQ', hreach, hC, -⟩ := exists_generator_eq_of_reachable hQ ha
  obtain ⟨w, hw⟩ := exists_isStationaryDistribution hQ' hreach
  refine ⟨w, ?_⟩
  have h := hw.tendsto_vecMul_transition hQ' hreach (p := Pi.single a 1) (by simp)
  refine h.congr fun t => ?_
  ext j
  rw [single_one_vecMul]
  exact transition_apply_eq_of_forall_eq (S := {b | Reachable Q a b})
    (fun i j hi hj => hQ.eq_zero_of_reachable_of_not_reachable hi hj)
    (fun i j hi => hC i j hi) t (Reachable.refl Q a) j

private theorem transition_apply_le_one (hQ : IsGenerator Q) {t : ℝ} (ht : 0 ≤ t)
    (i j : ι) : transition Q t i j ≤ 1 := by
  have hM := hQ.transition_mem_rowStochastic t ht
  rw [← Matrix.sum_row_of_mem_rowStochastic hM i]
  exact Finset.single_le_sum (f := fun l => transition Q t i l) (fun l _ => hM.1 i l)
    (Finset.mem_univ j)

/-- If no rate leads out of `S` and `S` can be reached from every state, then from every
state the probability of being outside `S` becomes as small as one likes. -/
private theorem exists_mulVec_indicator_lt (hQ : IsGenerator Q) {S : Set ι}
    (hS : ∀ a b, a ∈ S → b ∉ S → Q a b = 0) (hreach : ∀ i, ∃ a ∈ S, Reachable Q i a)
    (i : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 ≤ s ∧ (transition Q s *ᵥ Sᶜ.indicator 1) i < ε := by
  set x : ι → ℝ := Sᶜ.indicator 1 with hx
  have hxS : ∀ k, k ∈ S → x k = 0 := fun k hk => by simp [hx, hk]
  have hxN : ∀ k, k ∉ S → x k = 1 := fun k hk => by simp [hx, hk]
  have hx1 : ∀ k, x k ≤ 1 := fun k => by
    by_cases hk : k ∈ S
    · rw [hxS k hk]; exact zero_le_one
    · rw [hxN k hk]
  have hmv : ∀ (M : Matrix ι ι ℝ) (y : ι → ℝ) (k : ι), (M *ᵥ y) k = ∑ j, M k j * y j :=
    fun _ _ _ => rfl
  have hadd : ∀ s t : ℝ,
      transition Q (s + t) *ᵥ x = transition Q s *ᵥ (transition Q t *ᵥ x) := fun s t => by
    rw [transition_add, mulVec_mulVec]
  -- the mass outside `S` is zero from inside `S` and at most one from outside
  have hle : ∀ s : ℝ, 0 ≤ s → ∀ k, (transition Q s *ᵥ x) k ≤ x k := by
    intro s hs k
    have hM := hQ.transition_mem_rowStochastic s hs
    rw [hmv]
    by_cases hk : k ∈ S
    · rw [hxS k hk]
      refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
      by_cases hj : j ∈ S
      · rw [hxS j hj, mul_zero]
      · rw [transition_apply_eq_zero_of_forall_eq_zero hS s hk hj, zero_mul]
    · rw [hxN k hk, ← Matrix.sum_row_of_mem_rowStochastic hM k]
      exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hM.1 k j) (hx1 j)
  -- it does not grow with time
  have hmono : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ k,
      (transition Q (s + t) *ᵥ x) k ≤ (transition Q s *ᵥ x) k := by
    intro s t hs ht k
    rw [hadd, hmv _ (transition Q t *ᵥ x), hmv _ x]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle t ht j)
      ((hQ.transition_mem_rowStochastic s hs).1 k j)
  -- from every state it is below one at some time
  have hlt : ∀ k, ∃ τ : ℝ, 0 ≤ τ ∧ (transition Q τ *ᵥ x) k < 1 := by
    intro k
    obtain ⟨a, haS, τ, hτ⟩ := hreach k
    have hM := hQ.transition_mem_rowStochastic τ τ.coe_nonneg
    refine ⟨τ, τ.coe_nonneg, ?_⟩
    rw [hmv, ← Matrix.sum_row_of_mem_rowStochastic hM k]
    refine Finset.sum_lt_sum (fun j _ => mul_le_of_le_one_right (hM.1 k j) (hx1 j))
      ⟨a, Finset.mem_univ a, ?_⟩
    rw [hxS a haS, mul_zero]
    exact hτ
  choose τ hτ0 hτ1 using hlt
  -- so it is below one from every state at one common time
  obtain ⟨t₀, ht₀, hc⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ k, (transition Q t₀ *ᵥ x) k < 1 := by
    refine ⟨∑ k, τ k, Finset.sum_nonneg fun k _ => hτ0 k, fun k => ?_⟩
    have hrest : 0 ≤ ∑ l, τ l - τ k :=
      sub_nonneg.2 (Finset.single_le_sum (fun l _ => hτ0 l) (Finset.mem_univ k))
    rw [show ∑ l, τ l = τ k + (∑ l, τ l - τ k) by ring]
    exact (hmono _ _ (hτ0 k) hrest k).trans_lt (hτ1 k)
  -- and below one common factor
  obtain ⟨c, hc0, hc1, hcle⟩ :
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ k, (transition Q t₀ *ᵥ x) k ≤ c * x k := by
    have : Nonempty ι := ⟨i⟩
    obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => (transition Q t₀ *ᵥ x) k
    have hnn : 0 ≤ (transition Q t₀ *ᵥ x) k₀ := by
      rw [hmv]
      refine Finset.sum_nonneg fun j _ =>
        mul_nonneg ((hQ.transition_mem_rowStochastic t₀ ht₀).1 k₀ j) ?_
      by_cases hj : j ∈ S
      · rw [hxS j hj]
      · rw [hxN j hj]; exact zero_le_one
    refine ⟨_, hnn, hc k₀, fun k => ?_⟩
    by_cases hk : k ∈ S
    · have h := hle t₀ ht₀ k
      rw [hxS k hk] at h ⊢
      rwa [mul_zero]
    · rw [hxN k hk, mul_one]
      exact hk₀ k
  -- the factor applies once more with every further step of length `t₀`
  have hiter : ∀ n : ℕ, ∀ k, (transition Q (n * t₀) *ᵥ x) k ≤ c ^ n * x k := by
    intro n
    induction n with
    | zero =>
      intro k
      simp
    | succ n ih =>
      intro k
      rw [show ((n + 1 : ℕ) : ℝ) * t₀ = t₀ + n * t₀ by push_cast; ring, hadd,
        hmv _ (transition Q (n * t₀) *ᵥ x)]
      calc ∑ j, transition Q t₀ k j * (transition Q (n * t₀) *ᵥ x) j
          ≤ ∑ j, transition Q t₀ k j * (c ^ n * x j) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j)
              ((hQ.transition_mem_rowStochastic t₀ ht₀).1 k j)
        _ = c ^ n * (transition Q t₀ *ᵥ x) k := by
            rw [hmv _ x, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ c ^ n * (c * x k) := mul_le_mul_of_nonneg_left (hcle k) (pow_nonneg hc0 n)
        _ = c ^ (n + 1) * x k := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hc1
  refine ⟨n * t₀, mul_nonneg (Nat.cast_nonneg n) ht₀, ?_⟩
  calc (transition Q (n * t₀) *ᵥ x) i ≤ c ^ n * x i := hiter n i
    _ ≤ c ^ n * 1 := mul_le_mul_of_nonneg_left (hx1 i) (pow_nonneg hc0 n)
    _ < ε := by rwa [mul_one]

/-- If no rate leads out of `S`, `S` can be reached from every state, and the rows of the
states of `S` converge, then every row converges. -/
private theorem exists_tendsto_transition_row_of_closed (hQ : IsGenerator Q) {S : Set ι}
    (hS : ∀ a b, a ∈ S → b ∉ S → Q a b = 0) (hreach : ∀ i, ∃ a ∈ S, Reachable Q i a)
    (hlim : ∀ k ∈ S, ∃ L : ι → ℝ, Tendsto (fun t : ℝ => transition Q t k) atTop (𝓝 L))
    (i : ι) : ∃ L : ι → ℝ, Tendsto (fun t : ℝ => transition Q t i) atTop (𝓝 L) := by
  choose! L hL using hlim
  suffices h : ∀ j, ∃ l : ℝ, Tendsto (fun t : ℝ => transition Q t i j) atTop (𝓝 l) by
    choose l hl using h
    exact ⟨l, tendsto_pi_nhds.2 hl⟩
  intro j
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  obtain ⟨s₀, hs₀, hmass⟩ :=
    exists_mulVec_indicator_lt hQ hS hreach i (show 0 < ε / 4 by positivity)
  set x : ι → ℝ := Sᶜ.indicator 1 with hx
  have hxS : ∀ k, k ∈ S → x k = 0 := fun k hk => by simp [hx, hk]
  have hxN : ∀ k, k ∉ S → x k = 1 := fun k hk => by simp [hx, hk]
  have hM := hQ.transition_mem_rowStochastic s₀ hs₀
  -- after some time every row of `S` is close to its limit
  have hev : ∀ᶠ u : ℝ in atTop,
      0 ≤ u ∧ ∀ k, k ∈ S → |transition Q u k j - L k j| < ε / 4 := by
    refine (eventually_ge_atTop 0).and (eventually_all.2 fun k => ?_)
    by_cases hk : k ∈ S
    · have h := Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 (hL k hk) j) (ε / 4)
        (by positivity)
      filter_upwards [h] with u hu _
      rwa [Real.dist_eq] at hu
    · exact Eventually.of_forall fun u h => absurd h hk
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- so the entry is close to one fixed number from then on
  have hA : ∀ t : ℝ, s₀ + N ≤ t →
      |transition Q t i j - ∑ k, transition Q s₀ i k * ((1 - x k) * L k j)| < ε / 2 := by
    intro t ht
    obtain ⟨hu0, hu⟩ := hN (t - s₀) (by linarith)
    have hsplit : transition Q t i j =
        ∑ k, transition Q s₀ i k * transition Q (t - s₀) k j := by
      rw [← Matrix.mul_apply, ← transition_add, add_sub_cancel]
    have hterm : ∀ k, |transition Q (t - s₀) k j - (1 - x k) * L k j| ≤ x k + ε / 4 := by
      intro k
      by_cases hk : k ∈ S
      · rw [hxS k hk, sub_zero, one_mul, zero_add]
        exact (hu k hk).le
      · rw [hxN k hk, sub_self, zero_mul, sub_zero,
          abs_of_nonneg ((hQ.transition_mem_rowStochastic _ hu0).1 k j)]
        linarith [transition_apply_le_one hQ hu0 k j]
    calc |transition Q t i j - ∑ k, transition Q s₀ i k * ((1 - x k) * L k j)|
        = |∑ k, transition Q s₀ i k *
            (transition Q (t - s₀) k j - (1 - x k) * L k j)| := by
          rw [hsplit, ← Finset.sum_sub_distrib]
          simp only [mul_sub]
      _ ≤ ∑ k, transition Q s₀ i k *
            |transition Q (t - s₀) k j - (1 - x k) * L k j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (hM.1 i k)]
      _ ≤ ∑ k, transition Q s₀ i k * (x k + ε / 4) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hterm k) (hM.1 i k)
      _ = (transition Q s₀ *ᵥ x) i + ε / 4 := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
            Matrix.sum_row_of_mem_rowStochastic hM i, one_mul]
          rfl
      _ < ε / 2 := by linarith
  refine ⟨s₀ + N, fun t ht t' ht' => ?_⟩
  rw [Real.dist_eq]
  have h1 := hA t ht
  have h2 := hA t' ht'
  rw [abs_sub_comm] at h2
  exact (abs_sub_le _ _ _).trans_lt (by linarith)

/-- The transition matrices of a generator converge as time grows. No reachability
condition is needed. -/
theorem exists_tendsto_transition (hQ : IsGenerator Q) :
    ∃ L : Matrix ι ι ℝ, Tendsto (fun t : ℝ => transition Q t) atTop (𝓝 L) := by
  have hrow : ∀ i, ∃ L : ι → ℝ, Tendsto (fun t : ℝ => transition Q t i) atTop (𝓝 L) := by
    refine exists_tendsto_transition_row_of_closed hQ
      (S := {a | ∀ b, Reachable Q a b → Reachable Q b a}) ?_ ?_ ?_
    · intro a b ha hb
      by_contra hne
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      exact hb (hQ.forall_reachable_of_reachable ha
        (hQ.reachable_of_pos ((hQ.offDiag_nonneg a b hab).lt_of_ne' hne)))
    · intro i
      obtain ⟨a, hia, ha⟩ := hQ.exists_reachable_forall_reachable i
      exact ⟨a, ha, hia⟩
    · intro k hk
      exact exists_tendsto_transition_row hQ hk
  choose L hL using hrow
  exact ⟨L, tendsto_pi_nhds.2 hL⟩

/-- From every starting distribution, the distribution converges to a stationary
distribution. No reachability condition is needed. -/
theorem exists_isStationaryDistribution_tendsto (hQ : IsGenerator Q) {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ w : ι → ℝ, IsStationaryDistribution Q w ∧
      Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 w) := by
  obtain ⟨L, hL⟩ := exists_tendsto_transition hQ
  have hw : Tendsto (fun t : ℝ => p ᵥ* transition Q t) atTop (𝓝 (p ᵥ* L)) :=
    ((continuous_const.matrix_vecMul continuous_id).tendsto L).comp hL
  refine ⟨p ᵥ* L, ⟨fun i => ?_, ?_, IsInvariant.balance fun s _ => ?_⟩, hw⟩
  · exact ge_of_tendsto (tendsto_pi_nhds.1 hw i) (eventually_atTop.2 ⟨0, fun t ht =>
      Matrix.nonneg_vecMul_of_mem_rowStochastic (hQ.transition_mem_rowStochastic t ht) hp0 i⟩)
  · exact tendsto_nhds_unique (tendsto_finsetSum _ fun i _ => tendsto_pi_nhds.1 hw i)
      (tendsto_const_nhds.congr fun t => by rw [sum_vecMul_transition hQ, hp1])
  · have h1 : Tendsto (fun t : ℝ => (p ᵥ* transition Q t) ᵥ* transition Q s) atTop
        (𝓝 ((p ᵥ* L) ᵥ* transition Q s)) :=
      ((continuous_id.matrix_vecMul continuous_const).tendsto (p ᵥ* L)).comp hw
    have h2 : Tendsto (fun t : ℝ => (p ᵥ* transition Q t) ᵥ* transition Q s) atTop
        (𝓝 (p ᵥ* L)) := by
      simp_rw [← vecMul_transition_add]
      exact hw.comp (tendsto_atTop_add_const_right atTop s tendsto_id)
    exact tendsto_nhds_unique h1 h2

end SympyProofs.FiniteMarkovChain
