module

public import SympyProofs.Python.Cost.Erasure
public import SympyProofs.Binomial.Costs.PrimeExponent
public import SympyProofs.Binomial.Costs.ByteSieveErasure

/-! # Code equivalence of the complete costed prime-exponent kernel

`primeExponentsM_erases` proves that instrumentation preserves the original
imperative program. The proof matches the ordered generator outputs, each
quotient-loop transition, the conditional append, the product tree and the shift.
Only after this code equivalence is established does `primeExponentsM_run_eq_choose`
reuse the original algorithm's mathematical correctness theorem.

The policy and initial counter are arbitrary. The code-equivalence theorem only
needs a nonnegative upper argument for termination of the quotient loops. The
binomial specification additionally requires the original valid-input contract.
-/

@[expose] public section

open PythonInt Python.Cost
namespace SympyBinomial.PrimeExponent
variable (I : Type) [PythonInt I]

private theorem sequence_prod_erases (xs : Array I) :
    Erases (Sequence.prod xs) (Python.Math.prod xs) := by
  unfold Sequence.prod
  apply Erases.bind (a := Python.Math.prod xs)
  · rw [← Array.foldlM_toList]
    unfold Python.Math.prod
    rw [← Array.foldl_toList]
    apply Erases.foldlM xs.toList _ (fun a b => a*b)
    intro a b _
    exact (Erases.emit _).bind (Erases.perform _ _)
  · exact (Erases.emit _).bind (Erases.pure _)

private theorem balanced_rec_erases (factors : Array I) (leaf : ℕ) (hleaf : 0 < leaf)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ factors.size) :
    Erases (balancedFactorsM.rec (m := CostT Id) I factors leaf hleaf lo hi)
      (balancedFactors.rec I factors leaf hleaf lo hi) := by
  rw [balancedFactorsM.rec, balancedFactors.rec]
  apply (Erases.perform _ _).bind
  apply (Erases.perform _ _).bind
  by_cases h : hi-lo ≤ leaf
  · simp only [h,↓reduceIte]
    apply (Erases.perform _ _).bind
    have he : factors.extract lo hi = factors[lo:hi].toArray := by
      apply Array.toList_inj.mp
      simp [Subarray.toList_eq,Subarray.toList_toArray,Nat.min_eq_left hhi,Nat.min_eq_left hlo]
    rw [← he]
    exact sequence_prod_erases I _
  · simp only [h,↓reduceIte]
    apply (Erases.perform _ _).bind
    apply (Erases.perform _ _).bind
    apply (balanced_rec_erases factors leaf hleaf lo ((lo+hi)/2) (by omega) (by omega)).bind
    apply (balanced_rec_erases factors leaf hleaf ((lo+hi)/2) hi (by omega) hhi).bind
    exact Erases.perform _ _
termination_by hi-lo
decreasing_by all_goals omega

/-- The costed product preserves the same recursive splits and leaf products. -/
theorem balancedFactorsM_erases (factors : Array I) (leaf : ℕ := 32) (hleaf : 0 < leaf := by omega) :
    Erases (balancedFactorsM (m := CostT Id) I factors leaf hleaf) (balancedFactors I factors leaf hleaf) :=
  (Erases.perform _ _).bind (balanced_rec_erases I factors leaf hleaf 0 factors.size (by omega) (by omega))

private abbrev State := I × I × I × I
private abbrev CostState := CostExpr (CostT Id) I × CostExpr (CostT Id) I ×
  CostExpr (CostT Id) I × CostExpr (CostT Id) I
private def pack (s : State I) : CostState I :=
  (.value s.1, .value s.2.1, .value s.2.2.1, .value s.2.2.2)
private def step (p : I) (s : State I) : ForInStep (State I) :=
  let (a,b,c,e) := s
  if a != 0 then .yield (a/p,b/p,c/p,e+(a/p-b/p-c/p)) else .done s
private def costStep (p : I) (s : CostState I) : CostT Id (ForInStep (CostState I)) := do
  let (a,b,c,e) := s
  let p : CostExpr (CostT Id) I := .value p
  if !(← a.eq 0) then
    let a ← (a / p).eval
    let b ← (b / p).eval
    let c ← (c / p).eval
    let e ← (e + (a-b-c)).eval
    return .yield (a,b,c,e)
  else return .done (a,b,c,e)

private theorem costStep_erases (p : I) (s : State I) :
    Erases (costStep I p (pack I s))
      (match step I p s with | .done t => .done (pack I t) | .yield t => .yield (pack I t)) := by
  rcases s with ⟨a,b,c,e⟩
  intro model initial
  have hz : (0 : CostExpr (CostT Id) I).run = pure 0 := rfl
  have he : ((CostT.run (costStep I p (pack I (a,b,c,e))) model initial).1) =
      (if !(a == 0) then
        ForInStep.yield (pack I (a/p,b/p,c/p,e+(a/p-b/p-c/p)))
       else .done (pack I (a,b,c,e))) := by
    simp only [costStep,pack,CostExpr.eq,hz,CostExpr.run_value,LawfulMonad.pure_bind]
    change (CostT.run (do
      let test ← Python.Cost.Int.eq a 0
      if !test then _ else _ : CostT Id (ForInStep (CostState I))) model initial).1 = _
    rw [CostT.run_bind]
    change (CostT.run (if !(a == 0) then _ else _ : CostT Id (ForInStep (CostState I))) model _).1 = _
    split <;> rfl
  rw [he]
  simp only [step, bne]
  split <;> rfl

/-- The original inline quotient loop, named only to state its code equivalence. -/
private def quotientCode (n k p : I) : I := Id.run do
  let mut a := n
  let mut b := k
  let mut c := n-k
  let mut e := 0
  while a != 0 do
    a := a/p
    b := b/p
    c := c/p
    e := e+(a-b-c)
  return e

private theorem quotient_erases (n k : I) (p : ℕ) (hn : 0 ≤ toInt n) (hp : 2 ≤ p) :
    Erases (quotientExponentM (m := CostT Id) I n k (p:I)) (quotientCode I n k (p:I)) := by
  have hloop := Erases.loop (costStep I (p:I)) (step I (p:I)) (pack I)
    (fun s => 0 ≤ toInt s.1) (fun s => toNat s.1)
    (by intro s hs; cases he : step I (p:I) s <;> simpa only [he] using costStep_erases I (p:I) s) ?_ (n,k,n-k,0) hn
  · change Erases (do
      let c ← Python.Cost.Int.sub n k
      let s ← Lean.Loop.forIn ⟨⟩ (pack I (n,k,c,0)) (fun _ => costStep I (p:I))
      s.2.2.2.run) _
    apply (Erases.perform _ _).bind
    apply hloop.bind
    exact Erases.pure _
  · intro s t hs ht
    rcases s with ⟨a,b,c,e⟩
    simp only [step] at ht
    split at ht
    · rename_i h
      cases ht
      change 0 ≤ toInt a at hs
      have ha : toInt a ≠ 0 := by simpa using h
      have hd := toInt_div_of_nonneg a p hs (by omega)
      have hn := toNat_div_of_nonneg a p hs (by omega)
      exact ⟨by simp only [hd]; positivity, by
        simp only [hn]
        exact Nat.div_lt_self (by unfold toNat; omega) (by omega)⟩
    · contradiction

private def factorCode (n k : I) (prime : ℕ) (factors : Array I) : Array I :=
  let p : I := prime
  let e := quotientCode I n k p
  if e != 0 then factors.push (p ^ e) else factors

private theorem primeFactorM_erases (n k : I) (hn : 0 ≤ toInt n) (p : ℕ) (hp : 2 ≤ p)
    (factors : Array I) :
    Erases (primeFactorM (m := CostT Id) I n k p factors) (factorCode I n k p factors) := by
  have hz : (0 : CostExpr (CostT Id) I).run = pure 0 := rfl
  simp only [primeFactorM,CostExpr.eq,CostExpr.run_value,hz,LawfulMonad.pure_bind]
  apply (Erases.emit _).bind
  apply (quotient_erases I n k p hn hp).bind
  apply (Erases.perform _ _).bind
  unfold factorCode
  by_cases he : (quotientCode I n k (p:I) == 0) = true
  · simp only [he,Bool.not_true,bne]
    exact Erases.pure _
  · have hf : (quotientCode I n k (p:I) == 0) = false := Bool.eq_false_iff.mpr he
    simp only [hf,Bool.not_false,↓reduceIte,bne]
    change Erases (do
      let value ← Python.Cost.Int.pow (p:I) (quotientCode I n k (p:I))
      Sequence.append factors value) _
    exact (Erases.perform _ _).bind (Erases.perform _ _)

/-- Removing cost effects recovers the original imperative program, before using its specification. -/
theorem primeExponentsM_erases (B : Type) [PythonByteArray B] (n k : Value I)
    (hn : 0 ≤ toInt n) :
    Erases (primeExponentsM (m := CostT Id) I B n k) (primeExponents I B n k) := by
  have hz : (0 : CostExpr (CostT Id) I).run = pure 0 := rfl
  simp only [primeExponentsM,CostExpr.eq,CostExpr.run_value,hz,LawfulMonad.pure_bind]
  apply (Erases.perform _ _).bind
  by_cases hk : (k == 0) = true
  · simp only [primeExponents,hk,↓reduceIte]
    exact Erases.pure _
  · simp only [hk]
    apply (Erases.perform _ _).bind
    have hloop := ByteSieve.oddPrimesCostStream_forIn_erases B (toNat n)
      (fun p factors => ForInStep.yield <$> primeFactorM (m := CostT Id) I n k p factors)
      (fun p factors => .yield (factorCode I n k p factors)) (by
        intro p hp hpn factors
        rw [map_eq_pure_bind]
        exact (primeFactorM_erases I n k hn p hp.two_le factors).bind (Erases.pure _)) #[]
    apply hloop.bind
    apply (Erases.emit _).bind
    apply (balancedFactorsM_erases I _).bind
    have hv : Erases (valuationM (m := CostT Id) I n k) (valuation I n k) := by
      intro model initial
      rw [valuation_run I n k model initial]
    apply hv.bind
    change Erases (Python.Cost.Int.shiftLeft _ _) _
    have he : primeExponents I B n k =
        balancedFactors I (Id.run (ForIn.forIn (ByteSieve.oddPrimesGenerator B (toNat n)) #[]
          (fun p factors => pure (ForInStep.yield (factorCode I n k p factors))))) <<< valuation I n k := by
      simp only [primeExponents,Bool.eq_false_iff.mpr hk,Bool.false_eq_true,↓reduceIte]
      dsimp only [Id.run,Bind.bind,Pure.pure]
      congr 3
      funext p factors
      change (if quotientCode I n k (p:I) != 0 then
        ForInStep.yield (factors.push ((p:I) ^ quotientCode I n k (p:I)))
        else .yield factors) = .yield (factorCode I n k p factors)
      by_cases h : (quotientCode I n k (p:I) != 0) = true <;> simp only [factorCode,h,Bool.false_eq_true,↓reduceIte]
    rw [he]
    exact Erases.perform _ _

/-- Every policy and initial counter preserve the original kernel's result. -/
theorem primeExponentsM_run_eq (B : Type) [PythonByteArray B] (n k : Value I)
    (hn : 0 ≤ toInt n) (model : Model) (initial : ℕ) :
    (CostT.run (primeExponentsM (m := CostT Id) I B n k) model initial).1 =
      primeExponents I B n k := primeExponentsM_erases I B n k hn model initial

/-- The full costed kernel inherits the verified binomial specification. -/
theorem primeExponentsM_run_eq_choose (B : Type) [PythonByteArray B] (n k : Value I)
    (hk0 : 0 ≤ toInt k) (hk : toInt k ≤ toInt n) (model : Model) (initial : ℕ) :
    toInt (CostT.run (primeExponentsM (m := CostT Id) I B n k) model initial).1 =
      ((toNat n).choose (toNat k) : ℤ) := by
  rw [primeExponentsM_run_eq I B n k (by omega) model initial]
  exact primeExponents_eq_choose I B n k hk0 hk
end SympyBinomial.PrimeExponent
