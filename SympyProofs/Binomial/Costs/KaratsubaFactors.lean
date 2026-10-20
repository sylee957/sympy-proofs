module

public import SympyProofs.Binomial.Costs.PrimeStreamBounds
public import SympyProofs.Binomial.Costs.PrimeFactors
public import SympyProofs.Python.Cost.Karatsuba.Model

/-! # Factor count and individual widths from the executed sieve-consumer loop -/

@[expose] public section
open Python.Cost Python.Cost.Models PythonInt Generator
namespace SympyBinomial.PrimeExponent
variable (I B : Type) [PythonInt I] [PythonByteArray B]

def collectionBudget (n : ℕ) : ℕ :=
  128*(n.sqrt+1)*(n+1+inputWidth n^2)+4*(n+1+inputWidth n^2)+
    (n+1)*(64*(1+inputWidth n^2)+128*inputWidth n^3)

/-- Each emitted prime contributes at most one factor, whose width is at most
the input width. Events are charged directly by the consuming execution. -/
theorem factors_bounded_count (model : Model) (hmodel : ∀ e, model e ≤ schoolbook e)
    (n k : ℕ) (hk : k ≤ n) :
    Bounded model
      (ForIn.forIn (ByteSieve.oddPrimesCostStream B n) (#[] : Array I)
        (fun p factors => ForInStep.yield <$> primeFactorM (m := CostT Id) I (n:I) (k:I) p factors))
      (fun factors => factors.size ≤ n.primeCounting ∧
        ∀ x ∈ factors, width (toInt x) ≤ inputWidth n)
      (collectionBudget n) := by
  let inv (q : ℕ) (factors : Array I) :=
    factors.size ≤ q ∧ ∀ x ∈ factors, width (toInt x) ≤ inputWidth n
  let body : Event ⊕ ℕ → Array I → CostT Id (Array I) := fun entry factors =>
    match entry with
    | .inl event => do MonadCost.emit event; pure factors
    | .inr p => primeFactorM I (n:I) (k:I) p factors
  have hstep (q : ℕ) (factors : Array I) (hf : inv q factors)
      (entry : Event ⊕ ℕ) (hv : ByteSieve.primeAllowed n entry) :
      Bounded model (body entry factors)
        (inv (q+ByteSieve.traceMeasure (fun _ => 1) entry))
        (ByteSieve.traceWeight (128*inputWidth n^3) entry) := by
    cases entry with
    | inl event =>
      exact (RunsWith.perform (model := model) event factors).bounded
        (by simpa only [ByteSieve.traceMeasure,Nat.add_zero] using hf) (hmodel _)
    | inr p =>
      apply (primeFactorM_bounded_of_le I model hmodel n k p hk hv.1 hv.2 factors).mono
      · intro r hr
        subst r
        by_cases hz : (n.choose k).factorization p = 0
        · simp only [hz,↓reduceIte]
          exact ⟨by dsimp [inv] at hf ⊢; omega, hf.2⟩
        · simp only [hz,↓reduceIte]
          constructor
          · simpa only [Array.size_push,ByteSieve.traceMeasure] using Nat.add_le_add_right hf.1 1
          · intro x hx
            rcases Array.mem_push.mp hx with hx | hx
            · exact hf.2 x hx
            · subst x
              rw [toInt_natCast]
              exact primePower_width_le n k p (lt_of_lt_of_le hv.1.pos hv.2)
      · rfl
  have htrace := ByteSieve.oddPrimesCostStream_budgeted_measure B (fun _ => 1) n
    (128*inputWidth n^3)
  have h := htrace.forIn_bounded (model := model) body inv hstep #[]
    (by simp [inv])
  have hmono := h.mono
    (post' := fun factors => factors.size ≤ n.primeCounting ∧
      ∀ x ∈ factors, width (toInt x) ≤ inputWidth n)
    (budget' := collectionBudget n)
    (fun factors hf => by
      obtain ⟨q,hq,hs,hb⟩ := hf
      have hq' : q ≤ (ByteSieve.slotsFrom B (ByteSieve.sieve B n) 1).length := by
        simpa using hq
      exact ⟨hs.trans (hq'.trans (ByteSieve.slots_length_le_primeCounting B n)), hb⟩) (le_refl _)
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
