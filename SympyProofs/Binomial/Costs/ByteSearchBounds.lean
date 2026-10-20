module

public import SympyProofs.Binomial.Costs.ByteSieveBounds
public import SympyProofs.Binomial.Costs.ByteSieveRefinement

/-! Finite search traces, including the final unsuccessful scan. -/

@[expose] public section
open Python.Cost Python.Cost.Models PythonByteArray Generator
namespace SympyBinomial.ByteSieve
variable (B : Type) [PythonByteArray B]
local instance : MonadCost (Generator.Computation (Event ⊕ ℕ)) := eventCost

private theorem advance_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n : ℕ) (bytes : B) (i : ℤ)
    (hs : size bytes ≤ n) (_hi : 0 ≤ i) (hib : i.toNat < size bytes)
    (hprime : allowed (.inr (2*i.toNat+1))) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (advanceM (m := Generator.Computation (Event ⊕ ℕ)) B (fun p => Generator.yield (.inr p)) bytes i)
      (fun r => r = find bytes 0x01 (i.toNat+1))
      (32*(n+1+PrimeExponent.inputWidth n^2)+price) (measure (2*i.toNat+1)) := by
  let W := PrimeExponent.inputWidth n
  have hw : 1 ≤ W := PrimeExponent.inputWidth_pos n
  have hwi : width (i.toNat : ℤ) ≤ W := width_mono (by simpa only [Int.natAbs_natCast] using (Nat.le_of_lt hib).trans hs)
  have hn : width (n : ℤ) = W := rfl
  have hwm : width ((2*i.toNat : ℕ) : ℤ) ≤ W+2 := by
    have h := width_mul (2 : ℤ) (i.toNat : ℤ)
    have htwo : width (2 : ℤ) = 2 := by decide
    rw [htwo] at h
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h.trans (by omega)
  have hwa : width ((2*i.toNat+1 : ℕ) : ℤ) ≤ W+3 := by
    have h := width_add ((2*i.toNat : ℕ) : ℤ) 1
    have h1 : width (1 : ℤ) = 1 := by decide
    rw [h1] at h
    simpa only [Nat.cast_add,Nat.cast_one] using h.trans (Nat.add_le_add_right (max_le hwm (by omega)) 1)
  have hwj : width ((i.toNat+1 : ℕ) : ℤ) ≤ W := width_mono (by simpa only [Int.natAbs_natCast] using (show i.toNat+1 ≤ n by omega))
  have hfind : (if find bytes 1 (i.toNat+1) = -1 then size bytes-(i.toNat+1)
      else (find bytes 1 (i.toNat+1)).toNat+1-(i.toNat+1)) ≤ n := by
    rcases find_spec bytes 1 (i.toNat+1) with h | h
    · rw [ite_eq_left h.1]; omega
    · rw [ite_eq_right (by omega)]; omega
  simp only [advanceM,perform,
    MonadCost.emit,Bind.bind,Pure.pure,Generator.bind,Generator.yield]
  refine ⟨_,_,by repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,rfl,?_,?_,?_⟩
  · simp [hallowed,hprime]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook,integerSchoolbook,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    norm_num only [Nat.cast_ofNat]
    have h1 : width (1 : ℤ) = 1 := by decide
    have h2 : width (2 : ℤ) = 2 := by decide
    rw [h1,h2]
    have hm1 : max (width ((2*i.toNat : ℕ) : ℤ)) 1 ≤ W+2 := max_le hwm (by omega)
    have hm2 : max (width (i.toNat : ℤ)) 1 ≤ W := max_le hwi hw
    have hw2 : W ≤ W^2 := Nat.le_self_pow (by omega) W
    change _ ≤ 32*(n+1+W^2)+price
    nlinarith only [hwi,hwm,hwa,hwj,hfind,hm1,hm2,hw2,hw]
  · simp [traceMeasure]

private theorem ne_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price : ℕ) (i : ℤ) (w : ℕ) (hi : width i ≤ w)
    (hw : 1 ≤ w) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (Index.ne (m := Generator.Computation (Event ⊕ ℕ)) i (-1))
      (fun r => r = decide (i ≠ -1)) (w+1) 0 := by
  apply perform_budgeted (model := schoolbook) _ _ rfl rfl (hallowed _)
  apply (RunsWith.perform _ _).bounded (post := fun r => r = decide (i ≠ -1)) rfl
  simp only [schoolbook,integerSchoolbook,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have h1 : width (-1 : ℤ) = 1 := by decide
  rw [h1]
  omega

/-- All resumes terminate, with a separate sum of the sizes of emitted values. -/
theorem search_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n : ℕ) (bytes : B) (hs : size bytes ≤ n)
    (start : ℕ) (hv : ∀ j ∈ slotsFrom B bytes start, allowed (.inr (2*j+1))) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (searchM (m := Generator.Computation (Event ⊕ ℕ)) B (fun p => Generator.yield (.inr p))
        bytes (find bytes 0x01 start)) (fun _ => True)
      ((size bytes+1-start+1)*(64*(n+1+PrimeExponent.inputWidth n^2)+price))
      (((slotsFrom B bytes start).map (fun j => measure (2*j+1))).sum) := by
  let W := PrimeExponent.inputWidth n
  let T := n+1+W^2
  let L := 64*T+price
  let i := find bytes 0x01 start
  have hw : 1 ≤ W := PrimeExponent.inputWidth_pos n
  have hwi : width i ≤ W := by
    rcases find_spec bytes 0x01 start with hf | hf
    · change width (find bytes 0x01 start) ≤ W
      rw [hf.1]
      exact hw
    · rw [show i = (i.toNat : ℤ) from (Int.toNat_of_nonneg hf.1).symm]
      apply width_mono
      simp only [Int.natAbs_natCast]
      dsimp [i]
      omega
  have ht := ne_budgeted measure allowed hallowed price i W hwi hw
  have htail : ∀ test, test = decide (i ≠ -1) →
      Budgeted (traceWeight price) (traceMeasure measure) allowed
        (if test then do
          let next ← advanceM B (fun p => Generator.yield (.inr p)) bytes i
          searchM B (fun p => Generator.yield (.inr p)) bytes next
         else pure ()) (fun _ => True)
        ((size bytes+1-start)*L+(32*T+price))
        (((slotsFrom B bytes start).map (fun j => measure (2*j+1))).sum) := by
    intro test ht
    subst test
    by_cases hz : i = -1
    · simp only [hz,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte]
      exact (Generator.Budgeted.pure (post := fun _ => True) () trivial).mono (fun _ _ => trivial) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [hz,ne_eq,not_false_eq_true,decide_true,↓reduceIte]
      have hf := find_spec bytes 0x01 start
      rcases hf with hf | hf
      · exact (hz hf.1).elim
      have hmem : i.toNat ∈ slotsFrom B bytes start :=
        (mem_slotsFrom B bytes start i.toNat).mpr ⟨hf.2.2.1,hf.2.1,hf.2.2.2.1⟩
      have ha := advance_budgeted B measure allowed hallowed price n bytes i hs hf.1 hf.2.2.1 (hv _ hmem)
      have hrec := search_budgeted measure allowed hallowed price n bytes hs (i.toNat+1) (by
        intro j hj
        apply hv j
        obtain ⟨hj,hstart,hbyte⟩ := (mem_slotsFrom B bytes _ j).mp hj
        exact (mem_slotsFrom B bytes _ j).mpr ⟨hj,by dsimp [i] at hstart; omega,hbyte⟩)
      have hbind := ha.bind
        (f := fun next => searchM B (fun p => Generator.yield (.inr p)) bytes next)
        (post' := fun _ => True)
        (d := (size bytes+1-(i.toNat+1)+1)*L)
        (r := ((slotsFrom B bytes (i.toNat+1)).map (fun j => measure (2*j+1))).sum)
        (by intro next hn; subst next; exact hrec)
      apply hbind.mono (fun _ _ => trivial)
      · have hdec : size bytes+1-(i.toNat+1)+1 ≤ size bytes+1-start := by dsimp [i]; omega
        have hm := Nat.mul_le_mul_right L hdec
        change 32*T+price+_ ≤ _
        omega
      · rw [slotsFrom_next B bytes start,ite_eq_right hz,List.map_cons,List.sum_cons]
  have hrun := ht.bind htail
  obtain ⟨a,xs,hr,hpost,hall,hcost,hcount⟩ := hrun
  refine ⟨a,xs,.skip (searchM_step B bytes i) hr,hpost,hall,?_,by simpa only [Nat.zero_add] using hcount⟩
  have hW : W ≤ W^2 := Nat.le_self_pow (by omega) W
  have hpay : W+1+(32*T+price) ≤ L := by dsimp [T,L]; omega
  change _ ≤ (size bytes+1-start+1)*L
  have hb : W+1+((size bytes+1-start)*L+(32*T+price)) ≤ (size bytes+1-start+1)*L := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  exact hcost.trans hb
termination_by size bytes+1-start
decreasing_by omega
end SympyBinomial.ByteSieve
