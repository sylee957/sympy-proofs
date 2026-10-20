module

public import SympyProofs.Binomial.Costs.KaratsubaRuntime
public import SympyProofs.Binomial.Costs.KaratsubaGrowth

/-!
# Full `O(n^(log 3 / log 2))` bound

The counter of the automatically instrumented prime-exponent kernel satisfies
this bound uniformly for every `0 ≤ k ≤ n`. Here `n` is the numeric upper
argument, not its bit length.

The policy is `Models.karatsuba`: only multiplication changes from the existing
schoolbook policy. Division, prime powers, buffer operations, allocation, and
control are still charged. The proof composes bounds on the actual generated
program with Chebyshev's estimate for the number of prime factors and elementary
growth estimates for the remaining phases.

This is an upper bound under that arithmetic policy. It neither tightens the
schoolbook policy to a subquadratic bound nor verifies CPython's multiplication
implementation or wall-clock runtime.
-/

@[expose] public section
open Python.Cost Python.Cost.Models Python.Cost.Karatsuba Asymptotics Filter
namespace SympyBinomial.PrimeExponent

theorem karatsubaBudget_isBigO :
    (fun n : ℕ => (karatsubaBudget n:ℝ)) =O[atTop] (fun n => (n:ℝ)^exponent) := by
  have h := ((sieveWork_isBigO.const_mul_left 256).add
    (wordWork_isBigO.const_mul_left 32768)).add
      (primeTree_work_isBigO.const_mul_left 200001)
  convert h using 1
  funext n
  simp only [karatsubaBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  ring

/-- A uniform Karatsuba-exponent upper bound on the complete generated execution. -/
theorem primeExponentsM_karatsuba_isBigO (I B : Type) [PythonInt I] [PythonByteArray B]
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n) :
    (fun n : ℕ =>
      ((CostT.run (primeExponentsM (m := CostT Id) I B (n:I) (k n:I)) karatsuba).2:ℝ))
      =O[atTop] (fun n => (n:ℝ)^(Real.log 3 / Real.log 2)) := by
  apply IsBigO.trans (g := fun n : ℕ => (karatsubaBudget n:ℝ)) ?_ karatsubaBudget_isBigO
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [] with n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (primeExponentsM_karatsuba_budgeted I B n (k n) (hk n)).cost_le

end SympyBinomial.PrimeExponent
