module

public import SympyProofs.Binomial.Costs.PrimeExponent
public import SympyProofs.Python.Cost.ComputationBounds
public import SympyProofs.Python.Cost.Asymptotics

/-!
# Asymptotics of the executed valuation expression

The upper bound is composed from the size/cost rules for its arithmetic tree.
For `W = max (width n) (width k)`, its schoolbook charge lies between `W` and
`29 * W`, even on signed inputs. Hence it is Θ(W), whereas its primitive-call
count is Θ(1). On valid binomial inputs `0 ≤ k ≤ n`, W is just the bit width of n.

These theorems describe the declared reference cost model, not CPython timings.
They cover the valuation component; no whole-kernel bound is asserted here.
-/

@[expose] public section

namespace SympyBinomial.PrimeExponent

open PythonInt Python.Cost Python.Cost.Models Asymptotics

variable (I : Type) [PythonInt I]

def valuationCost (model : Model) (n k : I) : ℕ :=
  (CostT.run (valuationM (m := CostT Id) I n k) model).2

/-- Compose operation contracts, including the sizes of intermediate results. -/
theorem valuation_schoolbook_le (n k : I) :
    valuationCost I schoolbook n k ≤ 29 * max (width (toInt n)) (width (toInt k)) := by
  let W := max (width (toInt n)) (width (toInt k))
  have hn : Sized (pure n) W 0 := Sized.value n (le_max_left _ _)
  have hk : Sized (pure k) W 0 := Sized.value k (le_max_right _ _)
  have h := ((hk.bitCount).add ((hn.sub hk).bitCount)).sub hn.bitCount
  apply h.cost_le.trans
  have hW : 1 ≤ W := (one_le_width (toInt n)).trans (le_max_left _ _)
  omega

/-- Reading the two input integers already costs at least their maximum width. -/
theorem width_le_valuation_schoolbook (n k : I) :
    max (width (toInt n)) (width (toInt k)) ≤ valuationCost I schoolbook n k := by
  simp [valuationCost, valuation_run, charge, valuationEvents, valuationInstrumented, Instrumentation.Checked.bind,
    Instrumentation.Checked.primitive, Instrumentation.Checked.pure,
    Instrumentation.Checked.pyBitCount, Instrumentation.Checked.pySub,
    Instrumentation.Checked.pyAdd, Instrumentation.Program.events, Instrumentation.Program.value,
    schoolbook, integerSchoolbook]
  omega

/-- A tight bound for any family of inputs and any limiting filter. -/
theorem valuation_isTheta_width {X : Type} (l : Filter X) (n k : X → I) :
    (fun x => (valuationCost I schoolbook (n x) (k x) : ℝ)) =Θ[l]
      (fun x => ((max (width (toInt (n x))) (width (toInt (k x))) : ℕ) : ℝ)) :=
  nat_isTheta_of_bounds 29 (fun x => width_le_valuation_schoolbook I (n x) (k x))
    (fun x => valuation_schoolbook_le I (n x) (k x))

theorem valuation_isTheta_upper_width {X : Type} (l : Filter X) (n k : X → I)
    (hk0 : ∀ x, 0 ≤ toInt (k x)) (hk : ∀ x, toInt (k x) ≤ toInt (n x)) :
    (fun x => (valuationCost I schoolbook (n x) (k x) : ℝ)) =Θ[l]
      (fun x => (width (toInt (n x)) : ℝ)) := by
  have hwidth (x : X) : width (toInt (k x)) ≤ width (toInt (n x)) := by
    apply width_mono
    have h0 := hk0 x
    have hkn := hk x
    omega
  simpa only [max_eq_left (hwidth _)] using valuation_isTheta_width I l n k

theorem valuation_operations_isTheta_one {X : Type} (l : Filter X) (n k : X → I) :
    (fun x => (valuationCost I operations (n x) (k x) : ℝ)) =Θ[l] (fun _ => (1 : ℝ)) := by
  simpa only [Nat.cast_one] using nat_isTheta_of_bounds (l := l)
    (f := fun x => valuationCost I operations (n x) (k x)) (g := fun _ => 1) 6
    (by intro x; simp [valuationCost, valuation_operations])
    (by intro x; simp [valuationCost, valuation_operations])

/-- For valid natural inputs this is logarithmic in the numerical upper argument. -/
theorem valuation_isTheta_log2 (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n) :
    (fun n : ℕ => (valuationCost I schoolbook (n : I) (k n : I) : ℝ)) =Θ[Filter.atTop]
      (fun n => ((n.log2 + 1 : ℕ) : ℝ)) := by
  simpa only [toInt_natCast, width_eq_log2_succ, Int.natAbs_natCast] using
    valuation_isTheta_upper_width I Filter.atTop (fun n : ℕ => (n : I)) (fun n => (k n : I))
      (by intro n; simp) (by intro n; simpa using hk n)

end SympyBinomial.PrimeExponent
