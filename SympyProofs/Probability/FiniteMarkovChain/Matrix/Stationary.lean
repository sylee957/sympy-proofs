module

public import SympyProofs.Probability.FiniteMarkovChain.Matrix.Generator

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Stationary rows of a matrix

`Balance Q w` is the balance equation `w ᵥ* Q = 0`. This file is about matrices and
row vectors only. The balance equation says nothing about the sign or the total mass
of `w`.

`IsStationaryDistribution Q w` adds them: `w` has nonnegative entries that sum to one
and solves the balance equation.

The balance equation is equivalent to invariance under `exp (t • Q)` for every
nonnegative time. The equivalence holds for every finite real square matrix.

`Process.Stationary` reads the balance equation on a process, and `Process.Limit`
shows that the limit of the law of a process is a stationary distribution.
-/

@[expose] public section

namespace SympyProofs.FiniteMarkovChain

open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-! ### The balance equation -/

/-- The balance equation of a generator, without probability constraints. -/
def Balance (Q : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  w ᵥ* Q = 0

/-- A stationary distribution of `Q`: a probability distribution on the states, written
as a row, that solves the balance equation. -/
structure IsStationaryDistribution (Q : Matrix ι ι ℝ) (w : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  sum_eq_one : ∑ i, w i = 1
  balance : Balance Q w

/-! ### Invariance under the transition matrix -/

variable [DecidableEq ι]

/-- Invariance is required only at the nonnegative times of a CTMC. -/
def IsInvariant (Q : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → w ᵥ* transition Q t = w

/-- A balanced row is unchanged by every transition matrix. -/
theorem Balance.isInvariant {Q : Matrix ι ι ℝ} {w : ι → ℝ} (h : Balance Q w) :
    IsInvariant Q w := fun t _ => vecMul_transition_of_vecMul_eq_zero h t

/-- The right derivative at zero recovers balance from nonnegative-time invariance. -/
theorem IsInvariant.balance {Q : Matrix ι ι ℝ} {w : ι → ℝ} (h : IsInvariant Q w) :
    Balance Q w := by
  have hd : HasDerivWithinAt (fun t => w ᵥ* transition Q t) (w ᵥ* Q) (Set.Ici 0) 0 := by
    simpa using (hasDerivAt_vecMul_transition Q w 0).hasDerivWithinAt (s := Set.Ici 0)
  have hc : HasDerivWithinAt (fun t => w ᵥ* transition Q t) 0 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) w).congr
      (fun t ht => h t ht) (by simp)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd hc

/-- Balance is exactly invariance under all nonnegative-time transitions. -/
theorem balance_iff_isInvariant (Q : Matrix ι ι ℝ) (w : ι → ℝ) :
    Balance Q w ↔ IsInvariant Q w :=
  ⟨Balance.isInvariant, IsInvariant.balance⟩

end SympyProofs.FiniteMarkovChain
