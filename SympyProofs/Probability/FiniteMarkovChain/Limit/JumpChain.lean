module

public import SympyProofs.Probability.FiniteMarkovChain.Limit.Balance

/-!
# Method: the jump chain

A chain with generator `Q` waits in state `i` for a time with rate `exitRate Q i`, and
then jumps to state `j` with probability `jumpMatrix Q i j`. The jump matrix is the
transition matrix of a chain in discrete time, the jump chain.

The method: solve `π ᵥ* jumpMatrix Q = π` for the jump chain, take `w` with
`π j = exitRate Q j * w j`, which means dividing `π j` by the rate of `j`, and give `w`
the total mass of the start `p`. This is `JumpChainMethod Q p w`.

The idea is that the share of time spent in a state is the share of visits times the
length of a stay, and a stay in `j` lasts `1 / exitRate Q j` on average.

The equations of this method are the equations of the balance method in other letters,
by `jumpChainMethod_iff_balanceMethod`. The reason is `IsGenerator.vecMul_eq_sub`:
`w ᵥ* Q` is `π ᵥ* jumpMatrix Q - π` for `π j = exitRate Q j * w j`. So the method gives
the limit when some state can be reached from every state, by
`isLimitFrom_iff_jumpChainMethod`.

A state that is never left has rate `0`. Its row of the jump matrix is zero here, and
the statements above still hold. But then `π j = exitRate Q j * w j` cannot be solved
for `w j` by a division, so the method as a recipe needs every rate to be positive.

For a process with the transition probabilities of `Q`, the same equations with its law
at time `0` as `p` give its limiting law, by
`isLimitingLaw_iff_jumpChainMethod`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The rate at which the chain leaves state `i`. -/
def exitRate (Q : Matrix ι ι ℝ) (i : ι) : ℝ := -Q i i

/-- The jump matrix: the probability that the next state is `j`, given that the chain
leaves state `i`. The row of a state that is never left is zero. -/
noncomputable def jumpMatrix (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then 0 else Q i j / exitRate Q i

/-- A rate is the exit rate times the jump probability. -/
theorem IsGenerator.apply_eq_exitRate_mul (hQ : IsGenerator Q) {i j : ι} (hij : i ≠ j) :
    Q i j = exitRate Q i * jumpMatrix Q i j := by
  simp only [jumpMatrix, hij, ite_false]
  by_cases h0 : exitRate Q i = 0
  · -- a state with exit rate zero has a zero row
    have hii : Q i i = 0 := by simpa [exitRate] using h0
    have hs : ∑ k ∈ Finset.univ.erase i, Q i k = 0 := by
      have h := Finset.add_sum_erase Finset.univ (fun k => Q i k) (Finset.mem_univ i)
      rw [hQ.row_sum_zero i, hii, zero_add] at h
      exact h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k hk =>
      hQ.offDiag_nonneg i k (Finset.ne_of_mem_erase hk).symm).1 hs j
        (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)
    rw [hz, h0, zero_mul]
  · field_simp

/-- The balance equation, read on the jump chain. -/
theorem IsGenerator.vecMul_eq_sub (hQ : IsGenerator Q) (w : ι → ℝ) :
    w ᵥ* Q = (fun j => exitRate Q j * w j) ᵥ* jumpMatrix Q - fun j => exitRate Q j * w j := by
  ext k
  simp only [vecMul, dotProduct, Pi.sub_apply]
  rw [← Finset.add_sum_erase Finset.univ (fun j => w j * Q j k) (Finset.mem_univ k),
    ← Finset.add_sum_erase Finset.univ (fun j => exitRate Q j * w j * jumpMatrix Q j k)
      (Finset.mem_univ k)]
  have hkk : jumpMatrix Q k k = 0 := by simp [jumpMatrix]
  have hrest : ∑ j ∈ Finset.univ.erase k, w j * Q j k =
      ∑ j ∈ Finset.univ.erase k, exitRate Q j * w j * jumpMatrix Q j k :=
    Finset.sum_congr rfl fun j hj => by
      rw [hQ.apply_eq_exitRate_mul (Finset.ne_of_mem_erase hj)]
      ring
  rw [hrest, hkk]
  simp only [exitRate]
  ring

/-- A stationary row of the jump chain, divided by the exit rates, with the total mass
of the start. -/
def JumpChainMethod (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  (∃ π : ι → ℝ, π ᵥ* jumpMatrix Q = π ∧ ∀ j, π j = exitRate Q j * w j) ∧
    ∑ i, w i = ∑ i, p i

/-- The jump chain method and the balance method have the same solutions. -/
theorem jumpChainMethod_iff_balanceMethod (hQ : IsGenerator Q) (p w : ι → ℝ) :
    JumpChainMethod Q p w ↔ BalanceMethod Q p w := by
  refine and_congr_left fun _ => ⟨?_, fun hw => ?_⟩
  · rintro ⟨π, hπ, hπw⟩
    obtain rfl : π = fun j => exitRate Q j * w j := funext hπw
    rw [hQ.vecMul_eq_sub, hπ, sub_self]
  · have h := hQ.vecMul_eq_sub w
    rw [hw] at h
    exact ⟨_, (sub_eq_zero.1 h.symm), fun _ => rfl⟩

/-- If some state can be reached from every state, the jump chain method gives the
limit. -/
theorem isLimitFrom_iff_jumpChainMethod (hQ : IsGenerator Q) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ JumpChainMethod Q p w :=
  (isLimitFrom_iff_balanceMethod hQ h p w).trans
    (jumpChainMethod_iff_balanceMethod hQ p w).symm

/-! ### For a process -/

section Process

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- If some state can be reached from every state, the jump chain method gives the limiting
law of a process, with its law at time `0` as the start. -/
theorem isLimitingLaw_iff_jumpChainMethod [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ JumpChainMethod Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).trans
    (isLimitFrom_iff_jumpChainMethod hQ h _ w)

end Process

end SympyProofs.FiniteMarkovChain
