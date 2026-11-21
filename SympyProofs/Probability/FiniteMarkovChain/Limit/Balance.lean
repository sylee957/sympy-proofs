module

public import SympyProofs.Probability.FiniteMarkovChain.LongRun.ProcessLimiting

/-!
# Method: the balance equation

Solve `w ᵥ* Q = 0` together with the condition that `w` has the same total mass as the
start `p`. For a distribution `p` that condition is `∑ i, w i = 1`. This is
`BalanceMethod Q p w`.

The method gives the limit when some state can be reached from every state, by
`isLimitFrom_iff_balanceMethod`. Then the answer does not depend on `p` beyond its total
mass. Without that condition the system has more than one solution.

For a process with the transition probabilities of `Q`, the same equations with its law
at time `0` as `p` give its limiting law, by
`isLimitingLaw_iff_balanceMethod`.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- The balance equation, with the total mass of the start. -/
def BalanceMethod (Q : Matrix ι ι ℝ) (p w : ι → ℝ) : Prop :=
  w ᵥ* Q = 0 ∧ ∑ i, w i = ∑ i, p i

/-- If some state can be reached from every state, the balance method gives the limit. -/
theorem isLimitFrom_iff_balanceMethod (hQ : IsGenerator Q) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀) (p w : ι → ℝ) :
    IsLimitFrom Q p w ↔ BalanceMethod Q p w := by
  constructor
  · exact fun hw => ⟨hw.balance hQ, hw.sum_eq hQ⟩
  · rintro ⟨hw, hs⟩
    obtain ⟨v, hv⟩ := exists_isStationaryDistribution hQ h
    have hL : IsLimitFrom Q p (p ᵥ* limitMatrix Q) :=
      tendsto_vecMul_transition_limitMatrix hQ p
    have h0 : (p ᵥ* limitMatrix Q) ᵥ* Q = 0 := hL.balance hQ
    have hv0 : v ᵥ* Q = 0 := hv.balance
    -- the difference to the limit has total mass zero, so adding it to `v` changes nothing
    have hb : Balance Q (w - p ᵥ* limitMatrix Q + v) := by
      change (w - p ᵥ* limitMatrix Q + v) ᵥ* Q = 0
      rw [add_vecMul, sub_vecMul, hw, h0, hv0, sub_zero, add_zero]
    have h1 : ∑ i, (w - p ᵥ* limitMatrix Q + v) i = 1 := by
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hs, hL.sum_eq hQ, sub_self, zero_add, hv.sum_eq_one]
    have he := Balance.eq_of_sum_eq_one hQ h hb hv.balance h1 hv.sum_eq_one
    have hw' : w = p ᵥ* limitMatrix Q := by
      have := add_eq_right.1 he
      exact sub_eq_zero.1 this
    rw [hw']
    exact hL

/-! ### For a process -/

section Process

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ι} {P : Measure Ω}
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- If some state can be reached from every state, the balance method gives the limiting
law of a process, with its law at time `0` as the start. -/
theorem isLimitingLaw_iff_balanceMethod [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hQ : IsGenerator Q) (ht : HasTransition Q X P) {j₀ : ι}
    (h : ∀ i, Reachable Q i j₀)
    (w : ι → ℝ) :
    IsLimitingLaw X P w ↔ BalanceMethod Q (fun i => P.real {ω | X 0 ω = i}) w :=
  (isLimitingLaw_iff_isLimitFrom hX hQ ht w).trans
    (isLimitFrom_iff_balanceMethod hQ h _ w)

end Process

end SympyProofs.FiniteMarkovChain
