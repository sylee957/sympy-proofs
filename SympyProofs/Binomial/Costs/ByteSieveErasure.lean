module

public import SympyProofs.Python.Cost.GeneratorErasure
public import SympyProofs.Binomial.Costs.ByteSieveBounds
public import SympyProofs.Binomial.Costs.ByteSieveRefinement

/-! # Ordered generator equivalence after hiding cost events

The trace proof follows each search and resume, then lifts to arbitrary consumers
with matching state transitions. It preserves early exit as well as full traversal.
-/

@[expose] public section

open Python.Cost PythonByteArray Generator
namespace SympyBinomial.ByteSieve
variable (B : Type) [PythonByteArray B]
local instance erasureEventCost : MonadCost (Generator.Computation (Event ⊕ ℕ)) := eventCost

private theorem sieve_yields (n : ℕ) :
    Yields (sieveM (m := Generator.Computation (Event ⊕ ℕ)) B n) (sieve B n) [] := by
  let allowed : Event ⊕ ℕ → Prop := fun e => match e with | .inl _ => True | .inr _ => False
  obtain ⟨bytes,es,hr,hb,ha,_⟩ := sieve_budgeted B (fun _ => 0) allowed (fun _ => trivial) 0 n
  rw [sieveM_id] at hb
  rcases hb with ⟨rfl,_⟩
  refine ⟨es,hr,?_⟩
  unfold values
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have h := ha e he
  cases e with
  | inl _ => rfl
  | inr _ => exact h.elim

private theorem advance_yields (bytes : B) (i : ℤ) :
    Yields (advanceM (m := Generator.Computation (Event ⊕ ℕ)) B
      (fun p => Generator.yield (.inr p)) bytes i)
      (find bytes 0x01 (i.toNat+1)) [2*i.toNat+1] := by
  simp only [advanceM,Index.mul,Index.add,Index.binary,BufferIndex.find,perform,
    MonadCost.emit,Bind.bind,Pure.pure,Generator.bind,Generator.yield]
  refine ⟨_,by repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,rfl⟩

private theorem search_cost_step (bytes : B) (i : ℤ) :
    (searchM (m := Generator.Computation (Event ⊕ ℕ)) B (fun p => Generator.yield (.inr p)) bytes i).step =
      .skip (do
        let test ← Index.ne i (-1)
        if test then
          let next ← advanceM B (fun p => Generator.yield (.inr p)) bytes i
          searchM B (fun p => Generator.yield (.inr p)) bytes next
        else pure ()) := by
  by_cases h : i = -1 <;>
    simp [searchM,ForIn.forIn,Computation.step,Index.ne,perform,MonadCost.emit,Bind.bind,Pure.pure,
      Generator.bind,Generator.yield,h,advanceM,Index.mul,Index.add,Index.binary,BufferIndex.find]

private theorem search_yields (bytes : B) (start : ℕ) :
    Yields (searchM (m := Generator.Computation (Event ⊕ ℕ)) B (fun p => Generator.yield (.inr p))
      bytes (find bytes 0x01 start)) () ((slotsFrom B bytes start).map (fun j => 2*j+1)) := by
  apply Yields.skip (search_cost_step B bytes _)
  have ht : Yields (Index.ne (m := Generator.Computation (Event ⊕ ℕ)) (find bytes 0x01 start) (-1))
      (decide (find bytes 0x01 start ≠ -1)) [] := Yields.perform _ _
  have htail : Yields (if decide (find bytes 0x01 start ≠ -1) then do
      let next ← advanceM B (fun p => Generator.yield (.inr p)) bytes (find bytes 0x01 start)
      searchM B (fun p => Generator.yield (.inr p)) bytes next
    else pure ()) () ((slotsFrom B bytes start).map (fun j => 2*j+1)) := by
    rw [slotsFrom_next]
    by_cases hz : find bytes 0x01 start = -1
    · simp only [hz,ne_eq,not_true_eq_false,decide_false,↓reduceIte,List.map_nil]
      exact Yields.pure ()
    · simp only [hz,ne_eq,not_false_eq_true,decide_true,↓reduceIte,List.map_cons]
      exact (advance_yields B bytes _).bind (search_yields bytes ((find bytes 0x01 start).toNat+1))
  exact ht.bind htail
termination_by size bytes+1-start
decreasing_by
  rcases find_spec bytes 0x01 start with hf | hf
  · exact (hz hf.1).elim
  · omega

/-- Cost instrumentation emits exactly the same ordered prime sequence as the original generator. -/
theorem oddPrimesCostStream_yields (n : ℕ) :
    Yields (oddPrimesCostStream B n).computation ()
      ((List.range (n+1)).filter (fun p => decide (p.Prime ∧ p ≠ 2))) := by
  have hstart : slotsFrom B (sieve B n) 1 =
      (List.range (size (sieve B n))).filter (fun j => getByte (sieve B n) j == 1) := by
    apply List.filter_congr
    intro j hj
    have hb := List.mem_range.mp hj
    by_cases hz : j = 0
    · subst j
      rw [sieve_spec B n 0 hb]
      simp [Nat.not_prime_one]
    · simp [show 1 ≤ j by omega]
  have hsearch := search_yields B (sieve B n) 1
  rw [hstart,sieve_slots_eq_primes B n] at hsearch
  apply Yields.skip rfl
  exact (sieve_yields B n).bind ((Yields.emit _).bind ((Yields.perform _ _).bind hsearch))

/-- The stream and original generator agree for every consumer whose operations erase. -/
theorem oddPrimesCostStream_forIn_erases {σ : Type} (n : ℕ)
    (body : ℕ → σ → CostT Id (ForInStep σ)) (f : ℕ → σ → ForInStep σ)
    (hbody : ∀ p, p.Prime → p ≤ n → ∀ s, Erases (body p s) (f p s)) (s : σ) :
    Erases (ForIn.forIn (oddPrimesCostStream B n) s body)
      (Id.run (ForIn.forIn (oddPrimesGenerator B n) s (fun p s => pure (f p s)))) := by
  rw [oddPrimesGenerator_forIn]
  exact (oddPrimesCostStream_yields B n).forIn_erases body f (by
    intro p hp s
    obtain ⟨hr,hp⟩ := List.mem_filter.mp hp
    have hprime := of_decide_eq_true hp
    exact hbody p hprime.1 (by have := List.mem_range.mp hr; omega) s) s
end SympyBinomial.ByteSieve
