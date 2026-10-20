module

public import SympyProofs.Binomial.Costs.ByteSearchBounds
public import SympyProofs.Binomial.Costs.FactorBounds
public import Mathlib.NumberTheory.PrimeCounting

/-! Complete sieve stream: execution budget and prime-power payload bound. -/

@[expose] public section
open Python.Cost Python.Cost.Models PythonByteArray Generator
namespace SympyBinomial.ByteSieve
variable (B : Type) [PythonByteArray B]
local instance : MonadCost (Generator.Computation (Event ⊕ ℕ)) := eventCost

def primeMeasure (n k p : ℕ) : ℕ := width ((p^(n.choose k).factorization p : ℕ) : ℤ)
def primeAllowed (n : ℕ) : Event ⊕ ℕ → Prop
  | .inl _ => True
  | .inr p => p.Prime ∧ p ≤ n

private theorem slot_measure_le (n k : ℕ) :
    (((slotsFrom B (sieve B n) 1).map (fun j => primeMeasure n k (2*j+1))).sum) ≤
      PrimeExponent.factorBits n k := by
  have hstart : slotsFrom B (sieve B n) 1 =
      (List.range (size (sieve B n))).filter (fun j => getByte (sieve B n) j == 1) := by
    apply List.filter_congr
    intro j hj
    have hb := List.mem_range.mp hj
    by_cases hzero : j = 0
    · subst j
      rw [sieve_spec B n 0 hb]
      simp [Nat.not_prime_one]
    · simp [show 1 ≤ j by omega]
  rw [hstart]
  change (List.map (primeMeasure n k ∘ (fun j => 2*j+1)) _).sum ≤ _
  rw [← List.map_map, sieve_slots_eq_primes B n]
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  change _ ≤ ∑ p ∈ Finset.range (n+1), primeMeasure n k p
  apply Finset.sum_le_sum_of_subset
  intro p hp
  simpa using (List.mem_filter.mp (List.mem_toFinset.mp hp)).1

private theorem first_search_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n : ℕ) (bytes : B) (hs : size bytes ≤ n) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (do MonadCost.emit (.control "sieve.stop"); BufferIndex.find bytes 0x01 1 : Generator.Computation (Event ⊕ ℕ) ℤ)
      (fun r => r = find bytes 0x01 1) (4*(n+1+PrimeExponent.inputWidth n^2)) 0 := by
  have hf : (if find bytes 1 1 = -1 then size bytes-1 else (find bytes 1 1).toNat+1-1) ≤ n := by
    rcases find_spec bytes 1 1 with h | h
    · rw [ite_eq_left h.1]; omega
    · rw [ite_eq_right (by omega)]; omega
  simp only [BufferIndex.find,perform,MonadCost.emit,Bind.bind,Pure.pure,Generator.bind,Generator.yield]
  refine ⟨_,_,by repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,rfl,?_,?_,?_⟩
  · simp [hallowed]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook]
    have h1 : width (1 : ℤ) = 1 := by decide
    norm_num only [Nat.cast_one]
    rw [h1]
    omega
  · rfl

/-- A complete generator trace pays for the sieve and reserves `price` for each consumer call. -/
theorem oddPrimesCostStream_budgeted_measure (measure : ℕ → ℕ) (n price : ℕ) :
    Budgeted (traceWeight price) (traceMeasure measure) (primeAllowed n)
      (oddPrimesCostStream B n).computation (fun _ => True)
      (128*(n.sqrt+1)*(n+1+PrimeExponent.inputWidth n^2)+
        4*(n+1+PrimeExponent.inputWidth n^2)+
        (n+1)*(64*(1+PrimeExponent.inputWidth n^2)+price))
      (((slotsFrom B (sieve B n) 1).map (fun j => measure (2*j+1))).sum) := by
  let W := PrimeExponent.inputWidth n
  simp only [oddPrimesCostStream, oddPrimesBodyM_eq]
  let T := n+1+W^2
  have hsize : size (sieve B n) = (n+1)/2 := size_sieve B n
  have hs : size (sieve B n) ≤ n := by rw [hsize]; omega
  have hv : ∀ j ∈ slotsFrom B (sieve B n) 1, primeAllowed n (.inr (2*j+1)) := by
    intro j hj
    obtain ⟨hj,_,hb⟩ := (mem_slotsFrom B _ _ _).mp hj
    have hprime : (2*j+1).Prime := by
      rw [sieve_spec B n j hj] at hb
      split_ifs at hb with hp
      · exact hp
      · contradiction
    refine ⟨hprime,?_⟩
    rw [hsize] at hj
    omega
  have hsearch := (search_budgeted_linear B measure (primeAllowed n) (fun _ => trivial)
    price n (sieve B n) hs 1 hv).mono (fun _ _ => trivial)
    (show (size (sieve B n)+1-1+1)*(64*(1+W^2)+price) ≤ (n+1)*(64*(1+W^2)+price) by
      apply Nat.mul_le_mul_right; omega) (le_refl _)
  have hf := first_search_budgeted B measure (primeAllowed n) (fun _ => trivial)
    price n (sieve B n) hs
  have htail := hf.bind
    (f := fun i => searchM B (fun p => Generator.yield (.inr p)) (sieve B n) i)
    (post' := fun _ => True) (d := (n+1)*(64*(1+W^2)+price)) (r := ((slotsFrom B (sieve B n) 1).map (fun j => measure (2*j+1))).sum)
    (by intro i hi; subst i; exact hsearch)
  have htable := sieve_budgeted_sqrt B measure (primeAllowed n) (fun _ => trivial) price n
  have hbody := htable.bind
    (f := fun bytes => do
      MonadCost.emit (.control "sieve.stop")
      let i ← BufferIndex.find bytes 0x01 1
      searchM B (fun p => Generator.yield (.inr p)) bytes i)
    (post' := fun _ => True) (d := 4*T+(n+1)*(64*(1+W^2)+price)) (r := ((slotsFrom B (sieve B n) 1).map (fun j => measure (2*j+1))).sum)
    (by intro bytes hb; rw [sieveM_id] at hb; rcases hb with ⟨rfl,_⟩; simpa only [LawfulMonad.bind_assoc,Nat.zero_add] using htail)
  obtain ⟨a,xs,hr,hpost,hallow,hcost,hmeasure⟩ := hbody
  refine ⟨a,xs,.skip rfl hr,hpost,hallow,?_,by simpa only [Nat.zero_add] using hmeasure⟩
  simpa only [Nat.zero_add, T, W, Nat.add_assoc] using hcost

/-- Conservative schoolbook corollary retained for existing clients. -/
theorem oddPrimesCostStream_budgeted (n k price : ℕ) :
    Budgeted (traceWeight price) (traceMeasure (primeMeasure n k)) (primeAllowed n)
      (oddPrimesCostStream B n).computation (fun _ => True)
      (256*(n+1)*(n+1+PrimeExponent.inputWidth n^2)+(n+1)*price)
      (PrimeExponent.factorBits n k) := by
  apply (oddPrimesCostStream_budgeted_measure B (primeMeasure n k) n price).mono
    (fun _ _ => trivial) ?_ (slot_measure_le B n k)
  have hs := Nat.sqrt_le_self n
  have h₁ := Nat.mul_le_mul_right (n+1+PrimeExponent.inputWidth n^2)
    (show 128*(n.sqrt+1) ≤ 128*(n+1) by omega)
  have h₂ := Nat.mul_le_mul_left (n+1)
    (show 64*(1+PrimeExponent.inputWidth n^2)+price ≤
      64*(n+1+PrimeExponent.inputWidth n^2)+price by omega)
  have h₃ := Nat.le_mul_of_pos_left (n+1+PrimeExponent.inputWidth n^2)
    (show 0 < n+1 by omega)
  nlinarith only [h₁,h₂,h₃]

/-- There are no more emitted odd primes than primes at most `n`. -/
theorem slots_length_le_primeCounting (n : ℕ) :
    (slotsFrom B (sieve B n) 1).length ≤ n.primeCounting := by
  have hstart : slotsFrom B (sieve B n) 1 =
      (List.range (size (sieve B n))).filter (fun j => getByte (sieve B n) j == 1) := by
    apply List.filter_congr
    intro j hj
    have hb := List.mem_range.mp hj
    by_cases hz : j = 0
    · subst j; rw [sieve_spec B n 0 hb]; simp [Nat.not_prime_one]
    · simp [show 1 ≤ j by omega]
  rw [hstart, ← List.length_map (f := fun j => 2*j+1), sieve_slots_eq_primes B n]
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply Finset.card_le_card
  intro p hp
  simp only [List.mem_toFinset,List.mem_filter,List.mem_range,Finset.mem_filter,Finset.mem_range] at hp ⊢
  exact ⟨hp.1, (of_decide_eq_true hp.2).1⟩

end SympyBinomial.ByteSieve
