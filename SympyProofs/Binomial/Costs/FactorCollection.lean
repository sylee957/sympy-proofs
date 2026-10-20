module

public import SympyProofs.Binomial.Costs.PrimeStreamBounds
public import SympyProofs.Binomial.Costs.PrimeFactors
public import SympyProofs.Binomial.Costs.BalancedFactors

/-! Transfer the complete sieve trace into the prime-factor consuming loop. -/

@[expose] public section
open Python.Cost Python.Cost.Models PythonInt Generator
namespace SympyBinomial.PrimeExponent
variable (I B : Type) [PythonInt I] [PythonByteArray B]

private def collected (q : ℕ) (factors : Array I) : Prop :=
  factors.size ≤ q ∧ Sequence.inputBits factors ≤ q

/-- The consuming loop is charged for both producer events and prime arithmetic. -/
theorem factors_bounded (n k : ℕ) (hk : k ≤ n) :
    Bounded schoolbook
      (ForIn.forIn (ByteSieve.oddPrimesCostStream B n) (#[] : Array I)
        (fun p factors => ForInStep.yield <$> primeFactorM (m := CostT Id) I (n:I) (k:I) p factors))
      (fun factors => factors.size ≤ factorBits n k ∧ Sequence.inputBits factors ≤ factorBits n k)
      (256*(n+1)*(n+1+inputWidth n^2)+128*(n+1)*inputWidth n^3) := by
  let body : Event ⊕ ℕ → Array I → CostT Id (Array I) := fun entry factors =>
    match entry with
    | .inl event => do MonadCost.emit event; pure factors
    | .inr p => primeFactorM I (n:I) (k:I) p factors
  have hstep (q : ℕ) (factors : Array I) (hf : collected I q factors)
      (entry : Event ⊕ ℕ) (hv : ByteSieve.primeAllowed n entry) :
      Bounded schoolbook (body entry factors)
        (collected I (q+ByteSieve.traceMeasure (ByteSieve.primeMeasure n k) entry))
        (ByteSieve.traceWeight (128*inputWidth n^3) entry) := by
    cases entry with
    | inl event =>
      exact (RunsWith.perform (model := schoolbook) event factors).bounded
        (by simpa only [ByteSieve.traceMeasure,Nat.add_zero] using hf) (le_refl _)
    | inr p =>
      apply (primeFactorM_bounded I n k p hk hv.1 hv.2 factors).mono
      · intro r hr
        subst r
        by_cases hz : (n.choose k).factorization p = 0
        · simp only [hz,↓reduceIte]
          exact ⟨hf.1.trans (Nat.le_add_right _ _),hf.2.trans (Nat.le_add_right _ _)⟩
        · simp only [hz,↓reduceIte]
          have hw : 1 ≤ ByteSieve.primeMeasure n k p := Nat.le_max_left _ _
          constructor
          · simp only [Array.size_push]
            change factors.size+1 ≤ q+ByteSieve.primeMeasure n k p
            exact Nat.add_le_add hf.1 hw
          · simpa only [Sequence.inputBits,Array.toList_push,List.map_append,List.sum_append,
              List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,toInt_natCast,
              ByteSieve.traceMeasure,ByteSieve.primeMeasure] using
              Nat.add_le_add_right hf.2 (ByteSieve.primeMeasure n k p)
      · rfl
  have h := (ByteSieve.oddPrimesCostStream_budgeted B n k (128*inputWidth n^3)).forIn_bounded
    (model := schoolbook) body (collected I) hstep #[] (by simp [collected,Sequence.inputBits])
  have hmono := h.mono
    (post' := fun factors => factors.size ≤ factorBits n k ∧ Sequence.inputBits factors ≤ factorBits n k)
    (budget' := 256*(n+1)*(n+1+inputWidth n^2)+128*(n+1)*inputWidth n^3)
    (fun factors hf => by
    obtain ⟨q,hq,hs,hb⟩ := hf
    exact ⟨hs.trans hq,hb.trans hq⟩) (by ring_nf; rfl)
  have hstream {α V : Type} (stream : Stream V) (init : α) (body : V → α → CostT Id (ForInStep α)) :
      ForIn.forIn stream init body =
        ForIn.forIn stream.computation init (fun entry state =>
          match entry with
          | .inl event => do MonadCost.emit event; pure (.yield state)
          | .inr value => body value state) := rfl
  rw [hstream]
  convert hmono using 1
  congr 1
  funext entry factors
  cases entry <;> simp only [body,map_eq_pure_bind,LawfulMonad.bind_assoc,LawfulMonad.pure_bind]
end SympyBinomial.PrimeExponent
