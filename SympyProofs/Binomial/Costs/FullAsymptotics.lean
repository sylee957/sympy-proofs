module

public import SympyProofs.Binomial.Costs.FactorCollection
public import SympyProofs.Binomial.Costs.FinishBounds
public import SympyProofs.Binomial.Costs.PrimeExponentErasure

/-!
# Full runtime bound for the executed prime-exponent kernel

`primeExponentsM_schoolbook_le` bounds the counter returned by the actual costed
program: for every `k ≤ n`, its charge is at most `131072 * (n + 1)^2`.
`primeExponentsM_isBigO` gives the uniform asymptotic consequence. The `k = 0`
short circuit costs exactly two units by `primeExponentsM_zero_run`.
`primeExponentsM_correct_bounded` combines the runtime bound with the binomial
result, using the separate code-equivalence proof in `PrimeExponentErasure`.

The proof composes contracts for table initialization and marking, every generator
resume including exhaustion, the quotient loops, prime powers and list appends,
the balanced product tree and leaf allocations, popcounts, and the final shift.
The generator carries both an execution budget and an output-size measure. Its
consumer therefore receives a proved bound on the total factor width, which pays
for the product tree's arithmetic. Integer arithmetic charges depend on operand
and result widths.

This is a conservative upper bound under `Models.schoolbook`, not a tight bound
or a theorem about CPython wall time. The model charges logical allocation payload
and amortized append work; it does not model a particular allocator or collector.
Here `n` is the numeric upper argument, not the binary input length. Component
bounds are separate reusable theorems in `FactorCollection` and `FinishBounds`.
-/

@[expose] public section
open Python.Cost Python.Cost.Models PythonInt
namespace SympyBinomial.PrimeExponent
variable (I B : Type) [PythonInt I] [PythonByteArray B]

/-- Actual execution, including producer, consumer, allocation, arithmetic and return. -/
theorem primeExponentsM_bounded (n k : ℕ) (hk : k ≤ n) :
    Bounded schoolbook (primeExponentsM (m := CostT Id) I B (n:I) (k:I))
      (fun _ => True) (131072*(n+1)^2) := by
  let W := inputWidth n
  let N := n+1
  let C := 256*N*(N+W^2)+128*N*W^3
  let F := 1+(73792*N^2+64*N)
  have hw : 1 ≤ W := inputWidth_pos n
  have hkn : width (toInt (k:I)) ≤ W := by
    rw [toInt_natCast]
    apply width_mono
    simpa only [Int.natAbs_natCast] using hk
  have hzero : width (toInt (0:I)) ≤ W := by simpa [width] using hw
  have hfinish (factors : Array I) (hs : factors.size ≤ factorBits n k)
      (hb : Sequence.inputBits factors ≤ factorBits n k) :
      Bounded schoolbook (do
        MonadCost.emit (.control "primes.stop")
        let value ← balancedFactorsM (m := CostT Id) I factors
        let shift ← valuationM I (n:I) (k:I)
        Python.Cost.Int.shiftLeft value shift) (fun _ => True) F := by
    have hp := (product_finish_bounded I n k hk factors hs hb).bind
      (next := fun value => do
        let shift ← valuationM I (n:I) (k:I)
        Python.Cost.Int.shiftLeft value shift)
      (post' := fun _ => True) (d := 64*N)
      (fun value hv => valuation_shift_bounded I n k hk value hv)
    exact ((RunsWith.emit (model := schoolbook) (.control "primes.stop")).bounded
      (post := fun _ => True) trivial (le_refl _)).bind (fun _ _ => hp)
  have hloop := (factors_bounded I B n k hk).bind
    (next := fun factors => do
      MonadCost.emit (.control "primes.stop")
      let value ← balancedFactorsM (m := CostT Id) I factors
      let shift ← valuationM I (n:I) (k:I)
      Python.Cost.Int.shiftLeft value shift)
    (post' := fun _ => True) (d := F) (fun factors hf => hfinish factors hf.1 hf.2)
  have he : Bounded schoolbook (Sequence.empty (m := CostT Id) (α := I))
      (fun factors => factors = #[]) 1 :=
    (RunsWith.perform _ _).bounded rfl (le_refl _)
  have hinit := he.bind
    (next := fun factors => do
      let factors ← ForIn.forIn (ByteSieve.oddPrimesCostStream B n) factors
        (fun p factors => ForInStep.yield <$> primeFactorM (m := CostT Id) I (n:I) (k:I) p factors)
      MonadCost.emit (.control "primes.stop")
      let value ← balancedFactorsM (m := CostT Id) I factors
      let shift ← valuationM I (n:I) (k:I)
      Python.Cost.Int.shiftLeft value shift)
    (post' := fun _ => True) (d := C+F) (by intro factors hf; subst factors; exact hloop)
  have hguard := Python.Cost.Int.eq_bounded (k:I) 0 W hkn hzero
  have hmain := hguard.bind
    (next := fun (test : Bool) => (if test then pure (1:I) else do
      let factors ← Sequence.empty
      let factors ← ForIn.forIn (ByteSieve.oddPrimesCostStream B n) factors
        (fun p factors => ForInStep.yield <$> primeFactorM (m := CostT Id) I (n:I) (k:I) p factors)
      MonadCost.emit (.control "primes.stop")
      let value ← balancedFactorsM (m := CostT Id) I factors
      let shift ← valuationM I (n:I) (k:I)
      Python.Cost.Int.shiftLeft value shift : CostT Id I))
    (post' := fun _ => True) (d := 1+(C+F)) (by
      intro test _
      cases test
      · exact hinit
      · exact (Bounded.pure (post := fun _ => True) (1:I) trivial).mono (fun _ _ => trivial) (Nat.zero_le _))
  have hz : (0 : CostExpr (CostT Id) I).run = pure 0 := rfl
  have hshift (a b : I) :
      (CostExpr.value a <<< CostExpr.value b : CostExpr (CostT Id) I).run =
        Python.Cost.Int.shiftLeft a b := by rfl
  have hprogram : Bounded schoolbook (primeExponentsM (m := CostT Id) I B (n:I) (k:I))
      (fun _ => True) ((W+1)+(1+(C+F))) := by
    simpa only [primeExponentsM,CostExpr.eq,CostExpr.run_value,hz,hshift,
      LawfulMonad.pure_bind,toNat_natCast,bind_pure_comp] using hmain
  apply hprogram.mono (fun _ _ => trivial)
  have hcube : W^3 ≤ 8*N := inputWidth_cube_le n
  have hsquare : W^2 ≤ 8*N := (Nat.pow_le_pow_right hw (by omega : 2 ≤ 3)).trans hcube
  have hwN : W ≤ N := inputWidth_le n
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hm3 := Nat.mul_le_mul_left N hcube
  have hm2 := Nat.mul_le_mul_left N hsquare
  have hN2 : N ≤ N^2 := Nat.le_self_pow (by omega) N
  dsimp only [C,F]
  change W+1+(1+(256*N*(N+W^2)+128*N*W^3+(1+(73792*N^2+64*N)))) ≤ 131072*N^2
  nlinarith only [hm3,hm2,hwN,hN,hN2]

/-- The executed program returns the binomial coefficient within the proved budget. -/
theorem primeExponentsM_correct_bounded (n k : ℕ) (hk : k ≤ n) :
    Bounded schoolbook (primeExponentsM (m := CostT Id) I B (n:I) (k:I))
      (fun result => toInt result = (n.choose k : ℤ)) (131072*(n+1)^2) := by
  intro initial
  obtain ⟨value, cost, hr, _, hc⟩ := primeExponentsM_bounded I B n k hk initial
  refine ⟨value, cost, hr, ?_, hc⟩
  have hvalue := primeExponentsM_run_eq_choose I B (n:I) (k:I)
    (by simp) (by simpa using hk) schoolbook initial
  simpa only [hr, toNat_natCast] using hvalue

/-- Uniform quadratic bound on the actual counter, for every valid lower argument. -/
theorem primeExponentsM_schoolbook_le (n k : ℕ) (hk : k ≤ n) :
    (CostT.run (primeExponentsM (m := CostT Id) I B (n:I) (k:I)) schoolbook).2 ≤
      131072*(n+1)^2 := (primeExponentsM_bounded I B n k hk).cost_le

/-- A quadratic upper bound for the full executed kernel under the schoolbook policy. -/
theorem primeExponentsM_isBigO (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n) :
    (fun n : ℕ => ((CostT.run (primeExponentsM (m := CostT Id) I B (n:I) (k n:I)) schoolbook).2 : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (((n+1)^2 : ℕ) : ℝ)) :=
  nat_isBigO_of_le_mul 131072 (fun n => primeExponentsM_schoolbook_le I B n (k n) (hk n))
end SympyBinomial.PrimeExponent
