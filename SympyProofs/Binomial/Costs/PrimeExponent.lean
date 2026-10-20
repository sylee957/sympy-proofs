module

public import SympyProofs.Binomial.Algorithms.PrimeExponentCorrectness
public import SympyProofs.Python.Cost.Expr
public import SympyProofs.Python.Cost.Models
public import SympyProofs.Binomial.Costs.ByteSieve
public import SympyProofs.Python.Cost.Sequence

/-!
# Cost interpretation of prime-exponent evaluation

`valuationM` uses ordinary arithmetic instances on `CostExpr`. The original
algorithm stays unchanged. `valuationM_id` proves value equivalence, and
`valuation_trace` checks the exact evaluation order and operation events.
It makes six primitive calls, of which three are bit counts. This is a call count,
not constant bit complexity: the operands' widths remain in the events.
The complete kernel is instrumented by `primeExponentsM`, including the lazy sieve,
quotient loops, powers, list allocation, balanced multiplication and final shift.
`PrimeExponentErasure` proves equivalence of the complete costed program to the
original imperative kernel, for every charging policy and initial counter.
The complete executed counter is bounded in `FullAsymptotics`, using contracts for
the producer, consumer, and arithmetic phases. Valuation-specific asymptotics
are in `PrimeExponentAsymptotics`.
-/

@[expose] public section

universe v

namespace SympyBinomial.PrimeExponent

open PythonInt Python.Cost

variable (I : Type) [PythonInt I]

/-- Interpret the same formula with effectful arithmetic operations. -/
def valuationM {m : Type → Type v} [Monad m] [MonadCost m]
    (n k : Value I) : m I :=
  let n : CostExpr m I := CostExpr.value n
  let k : CostExpr m I := CostExpr.value k
  (k.bitCount + (n - k).bitCount - n.bitCount).run

/-- Erasing the instrumentation recovers the algorithm's formula. -/
theorem valuationM_id (n k : Value I) :
    valuationM (m := Id) I n k = valuation I n k := rfl

/-- Exact evaluation order of `k.bit_count() + (n-k).bit_count() - n.bit_count()`. -/
def valuationEvents (n k : Value I) : List Event :=
  let a := bitCount k
  let d := n - k
  let b := bitCount d
  let s := a + b
  let c := bitCount n
  [.integer ⟨.bitCount, [toInt k], toInt a⟩,
   .integer ⟨.sub, [toInt n, toInt k], toInt d⟩,
   .integer ⟨.bitCount, [toInt d], toInt b⟩,
   .integer ⟨.add, [toInt a, toInt b], toInt s⟩,
   .integer ⟨.bitCount, [toInt n], toInt c⟩,
   .integer ⟨.sub, [toInt s, toInt c], toInt (s - c)⟩]

/-- The trace records all six calls, including reused operands and intermediate results. -/
theorem valuation_trace (n k : Value I) :
    TraceT.run (valuationM (m := TraceT Id) I n k) =
      (valuation I n k, valuationEvents I n k) := rfl

/-- Every charging policy changes only cost, not the computed valuation. -/
theorem valuation_run (n k : Value I) (model : Model) (initial : ℕ := 0) :
    CostT.run (valuationM (m := CostT Id) I n k) model initial =
      (valuation I n k, initial + charge model (valuationEvents I n k)) := by
  change (valuation I n k,
    (valuationEvents I n k).foldl (fun total event => total + model event) initial) = _
  rw [foldl_charge]

/-- This exact count is independent of the integer magnitudes. -/
theorem valuation_operations (n k : Value I) :
    CostT.run (valuationM (m := CostT Id) I n k) Models.operations =
      (valuation I n k, 6) := by
  rw [valuation_run I n k Models.operations 0]
  simp [valuationEvents]

theorem valuation_bitCount_calls (n k : Value I) :
    charge (Models.integerCalls .bitCount) (valuationEvents I n k) = 3 := by
  simp [charge, valuationEvents, Models.integerCalls]

/-- Costed execution retains the established arithmetic correctness theorem. -/
theorem valuation_run_eq_factorization (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) (model : Model) :
    toInt (CostT.run (valuationM (m := CostT Id) I n k) model).1 =
      (((toNat n).choose (toNat k)).factorization 2 : ℤ) := by
  rw [valuation_run I n k model 0]
  exact valuation_eq_factorization I n k hk0 hk

/-- Costed balanced product, including leaf slices and index arithmetic. -/
def balancedFactorsM {m : Type → Type} [Monad m] [MonadCost m]
    (factors : Array I) (leaf : ℕ := 32) (hleaf : 0 < leaf := by omega) : m I := do
  let rec «rec» (lo hi : ℕ) : m I := do
    have : 0 < leaf := hleaf
    -- Values of indices remain pure so termination does not depend on the cost interpreter.
    let count := hi - lo
    let _ ← Index.sub hi lo
    let _ ← Index.le count leaf
    if count ≤ leaf then
      let xs ← Sequence.slice factors lo hi
      return ← Sequence.prod xs
    else
      let mid := (lo + hi) / 2
      let _ ← Index.add lo hi
      let _ ← Index.div (lo + hi) 2
      let a ← «rec» lo mid
      let b ← «rec» mid hi
      Python.Cost.Int.mul a b
  termination_by hi - lo
  decreasing_by all_goals omega
  let _ ← Sequence.length factors
  «rec» 0 factors.size

private theorem balancedFactorsM_rec_id (factors : Array I) (leaf : ℕ)
    (hleaf : 0 < leaf) (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ factors.size) :
    balancedFactorsM.rec (m := Id) I factors leaf hleaf lo hi =
      balancedFactors.rec I factors leaf hleaf lo hi := by
  rw [balancedFactorsM.rec, balancedFactors.rec]
  by_cases h : hi - lo ≤ leaf
  · simp only [h, ↓reduceIte]
    change Python.Math.prod (factors.extract lo hi) = Python.Math.prod (factors[lo:hi].toArray)
    congr 1
    apply Array.toList_inj.mp
    simp [Subarray.toList_eq, Subarray.toList_toArray,
      Nat.min_eq_left hhi, Nat.min_eq_left hlo]
  · simp only [h, ↓reduceIte]
    change (Id.run (balancedFactorsM.rec (m := Id) I factors leaf hleaf lo ((lo + hi) / 2))) *
      (Id.run (balancedFactorsM.rec (m := Id) I factors leaf hleaf ((lo + hi) / 2) hi)) = _
    rw [balancedFactorsM_rec_id factors leaf hleaf lo ((lo + hi) / 2) (by omega) (by omega),
      balancedFactorsM_rec_id factors leaf hleaf ((lo + hi) / 2) hi (by omega) hhi]
    rfl
termination_by hi - lo
decreasing_by all_goals omega

theorem balancedFactorsM_id (factors : Array I) (leaf : ℕ := 32)
    (hleaf : 0 < leaf := by omega) :
    balancedFactorsM (m := Id) I factors leaf hleaf = balancedFactors I factors leaf hleaf := by
  exact balancedFactorsM_rec_id I factors leaf hleaf 0 factors.size (by omega) (by omega)

/-- The costed Legendre loop, preserving the imperative statement order. -/
def quotientExponentM {m : Type → Type} [Monad m] [MonadCost m]
    (n k p : I) : m I := do
  let p : CostExpr m I := .value p
  let mut a : CostExpr m I := .value n
  let mut b : CostExpr m I := .value k
  let mut c ← (CostExpr.value n - CostExpr.value k : CostExpr m I).eval
  let mut e : CostExpr m I := 0
  while !(← a.eq 0) do
    a ← (a / p).eval
    b ← (b / p).eval
    c ← (c / p).eval
    e ← (e + (a - b - c)).eval
  e.run

/-- Consume one generated prime, including its quotient loop, power and possible append. -/
def primeFactorM {m : Type → Type} [Monad m] [MonadCost m]
    (n k : I) (prime : ℕ) (factors : Array I) : m (Array I) := do
  MonadCost.emit (.control "primes.next")
  let p : CostExpr m I := .value (prime : I)
  let exponent ← quotientExponentM I n k (prime : I)
  let e : CostExpr m I := .value exponent
  if !(← e.eq 0) then
    Sequence.append factors (← (p ^ e).run)
  else return factors

/-- Complete instrumented kernel. Values bound by `eval` are never re-evaluated. -/
def primeExponentsM (B : Type) [PythonByteArray B] {m : Type → Type} [Monad m] [MonadCost m]
    (n k : Value I) : m I := do
  let n : CostExpr m I := .value n
  let k : CostExpr m I := .value k
  if ← k.eq 0 then return 1
  let mut factors ← Sequence.empty
  for prime in ByteSieve.oddPrimesCostStream B (toNat (← n.run)) do
    factors ← primeFactorM I (← n.run) (← k.run) prime factors
  MonadCost.emit (.control "primes.stop")
  let result ← balancedFactorsM I factors
  let shift ← valuationM I (← n.run) (← k.run)
  (CostExpr.value result <<< CostExpr.value shift : CostExpr m I).run

/-- The complete execution takes only its initial equality test when `k = 0`.
In particular, it does not construct or resume the sieve. -/
theorem primeExponentsM_zero_run (B : Type) [PythonByteArray B] (n : I) (initial : ℕ) :
    CostT.run (primeExponentsM (m := CostT Id) I B n 0) Models.schoolbook initial =
      (1, initial + 2) := by
  have hz : (0 : CostExpr (CostT Id) I).run = pure 0 := rfl
  simp [hz, primeExponentsM, CostExpr.eq, CostExpr.value, Python.Cost.Int.eq,
    CostT.run, perform, MonadCost.emit]
  rfl

end SympyBinomial.PrimeExponent
