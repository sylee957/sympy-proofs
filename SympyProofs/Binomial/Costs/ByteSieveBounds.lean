module

public import SympyProofs.Binomial.Costs.ByteSieve
public import SympyProofs.Binomial.Costs.OperandBounds
/-!
# Executed sieve marking costs

A candidate produces a finite event trace, preserves its pure table update, and
costs `O(n + W²)`. This includes creating the immutable replacement bytes and
writing the slice. No primality assumption is needed for the candidate itself.
-/

@[expose] public section

open Python.Cost Python.Cost.Models PythonByteArray Generator
open scoped PythonBytes
namespace SympyBinomial.ByteSieve
variable (B : Type) [PythonByteArray B]
local instance : MonadCost (Generator.Computation (Event ⊕ ℕ)) := eventCost
/-- Price actual events and reserve a fixed budget for each consumed prime. -/
def traceWeight (price : ℕ) : Event ⊕ ℕ → ℕ
  | .inl e => schoolbook e
  | .inr _ => price
/-- Measure only emitted primes; event entries contribute zero. -/
def traceMeasure (measure : ℕ → ℕ) : Event ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr p => measure p
variable (measure : ℕ → ℕ)

private theorem mark_zero_budgeted (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price p : ℕ) (bytes : B) (hz : bytes[p/2]! = 0) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed (markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes)
      (fun r => r = Id.run (markM (m := Id) B p bytes) ∧ size r = size bytes) (16*(size bytes+1+(width (p : ℤ))^2)) 0 := by
  simp only [markM, Index.div, Index.binary, BufferIndex.get, perform, MonadCost.emit,
    Bind.bind, Pure.pure, Generator.bind, Generator.yield, hz, ne_self_iff_false,
    ↓reduceIte]
  refine ⟨_,_,by repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,?_,?_,?_,?_⟩
  · constructor
    · rfl
    · rfl
  · simp [hallowed]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook,integerSchoolbook,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    have hp := one_le_width (p : ℤ)
    have hd : width ((p/2 : ℕ) : ℤ) ≤ width (p : ℤ) :=
      width_mono (by simpa only [Int.natAbs_natCast] using Nat.div_le_self p 2)
    have h2 : width (2 : ℤ) = 2 := by decide
    norm_num only [Nat.cast_ofNat]
    rw [h2]
    nlinarith
  · rfl


set_option maxHeartbeats 1000000 in
private theorem mark_nonzero_budgeted (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n p : ℕ) (bytes : B) (hs : size bytes = (n+1)/2)
    (hp3 : 3 ≤ p) (hpodd : p%2 = 1) (hp2 : p*p ≤ n)
    (hnz : bytes[p/2]! ≠ 0) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed (markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes)
      (fun r => r = Id.run (markM (m := Id) B p bytes) ∧ size r = size bytes) (64*(n+1+(SympyBinomial.PrimeExponent.inputWidth n)^2)) 0 := by
  let W := SympyBinomial.PrimeExponent.inputWidth n
  let start := p*p/2
  let diff := size bytes-1-start
  let reps := diff/p+1
  have hodd : (p*p)%2 = 1 := by simp [Nat.mul_mod,hpodd]
  have hstart : start < size bytes := by dsimp [start]; omega
  have hn : 1 ≤ n := by nlinarith
  have hsize : size bytes ≤ n := by omega
  have hsub1 : len bytes-1 = ((size bytes-1 : ℕ) : ℤ) := by unfold len; omega
  have hsub2 : len bytes-1-(start : ℤ) = (diff : ℤ) := by unfold len; dsimp [diff]; omega
  have hquot : (len bytes-1-(start : ℤ)).fdiv p = ((diff/p : ℕ) : ℤ) := by
    rw [hsub2, ← Int.ofNat_fdiv]
  have hreps : (len bytes-1-(start : ℤ)).fdiv p+1 = (reps : ℤ) := by
    rw [hquot]; simp [reps]
  have hrsize : PythonBytes.size ((b[0] : Bytes B) * ((len bytes-1-(start : ℤ)).fdiv p+1)) = reps := by
    simp [hreps]
  have hrle : reps ≤ size bytes := by
    have hd := Nat.div_le_self diff p
    dsimp [reps,diff] at *
    omega
  have wn (a : ℕ) (ha : a ≤ n) : width (a : ℤ) ≤ W :=
    width_mono (by simpa only [Int.natAbs_natCast] using ha)
  have hw : 1 ≤ W := one_le_width (n : ℤ)
  have wp : width (p : ℤ) ≤ W := wn _ (by nlinarith)
  have wpp : width ((p*p : ℕ) : ℤ) ≤ W := wn _ hp2
  have wstart : width (start : ℤ) ≤ W := wn _ (by omega)
  have wsize : width (len bytes) ≤ W := wn _ hsize
  have ws1 : width (len bytes-1) ≤ W := by rw [hsub1]; exact wn _ (by omega)
  have wdiff : width (len bytes-1-(start : ℤ)) ≤ W := by rw [hsub2]; exact wn _ (by dsimp [diff]; omega)
  have wquot : width ((len bytes-1-(start : ℤ)).fdiv p) ≤ W := by
    rw [hquot]; exact wn _ ((Nat.div_le_self _ _).trans (by dsimp [diff]; omega))
  have wreps : width ((len bytes-1-(start : ℤ)).fdiv p+1) ≤ W := by
    rw [hreps]; exact wn _ (hrle.trans hsize)
  have windex : width ((p/2 : ℕ) : ℤ) ≤ W := wn _ ((Nat.div_le_self _ _).trans (by nlinarith))
  have h2 : width (2 : ℤ) = 2 := by decide
  have h1 : width (1 : ℤ) = 1 := by decide
  simp only [markM, Index.div, Index.mul, Index.binary, Index.signed, BufferIndex.get,
    BufferIndex.length, BufferIndex.literal, BufferIndex.repeatBytes, BufferIndex.setSlice,
    perform, MonadCost.emit, Bind.bind, Pure.pure, Generator.bind, Generator.yield]
  refine ⟨_,_,by
    iterate 4
      apply Returns.yield rfl
      apply Returns.skip rfl
    dsimp only
    rw [ite_eq_left hnz]
    repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,?_,?_,?_,?_⟩
  · constructor
    · change _ = if bytes[p/2]! ≠ 0 then _ else _
      rw [ite_eq_left hnz]
      rfl
    · split_ifs
      · exact PythonByteArray.size_setSlice _ _ _ _ _ _
      · rfl
      · rfl
  · simp [hallowed]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook,integerSchoolbook,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      PythonBytes.size_literal,Array.size_singleton,Nat.one_mul]
    norm_num only [Nat.cast_ofNat]
    change _ ≤ 64*(n+1+W^2)
    rw [h2,h1]
    have hrto : ((len bytes-1-(start : ℤ)).fdiv p+1).toNat = reps := by rw [hreps]; rfl
    simp only [show p*p/2 = start from rfl,hrto,hrsize]
    have hm := Nat.mul_le_mul wp wp
    have hd := Nat.mul_le_mul wdiff wp
    have hsquare : W ≤ W^2 := Nat.le_self_pow (by omega) W
    have hw2 : 1 ≤ W^2 := hw.trans hsquare
    simp only [pow_two] at hsquare hw2 ⊢
    clear hs hp3 hpodd hp2 hnz hodd hstart hn hsub1 hsub2 hquot hreps hrsize wn h2 h1 hrto
    omega
  · rfl
/-- Every candidate has a bounded finite event trace and preserves the pure table update. -/
theorem mark_budgeted (allowed : Event ⊕ ℕ → Prop) (hallowed : ∀ e, allowed (.inl e))
    (price n p : ℕ) (bytes : B) (hs : size bytes = (n+1)/2)
    (hp3 : 3 ≤ p) (hpodd : p%2 = 1) (hp2 : p*p ≤ n) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed (markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes)
      (fun r => r = Id.run (markM (m := Id) B p bytes) ∧ size r = size bytes)
      (64*(n+1+(SympyBinomial.PrimeExponent.inputWidth n)^2)) 0 := by
  by_cases hz : bytes[p/2]! = 0
  · have h := mark_zero_budgeted B measure allowed hallowed price p bytes hz
    apply h.mono (fun _ h => h) ?_ (le_refl _)
    have wp : width (p : ℤ) ≤ SympyBinomial.PrimeExponent.inputWidth n :=
      width_mono (by simp only [Int.natAbs_natCast]; nlinarith)
    have hm := Nat.pow_le_pow_left wp 2
    have hn : size bytes ≤ n+1 := by omega
    nlinarith only [hm,hn]
  · exact mark_nonzero_budgeted B measure allowed hallowed price n p bytes hs hp3 hpodd hp2 hz
/-- Table allocation, zeroing slot zero, and their arithmetic have a finite charged trace. -/
theorem initial_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop) (hallowed : ∀ e, allowed (.inl e))
    (price n : ℕ) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (initialM (m := Generator.Computation (Event ⊕ ℕ)) B n)
      (fun r => r = Id.run (initialM (m := Id) B n) ∧ size r = (n+1)/2)
      (32*(n+1+PrimeExponent.inputWidth n^2)) 0 := by
  let W := PrimeExponent.inputWidth n
  have hw : 1 ≤ W := PrimeExponent.inputWidth_pos n
  have hsum : width ((n+1 : ℕ) : ℤ) ≤ W+1 := by
    have h := width_add (n : ℤ) 1
    have h1 : width (1 : ℤ) = 1 := by decide
    have hnw : width (n : ℤ) = W := rfl
    rw [h1,hnw,max_eq_left hw] at h
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have hcount : width (((n+1)/2 : ℕ) : ℤ) ≤ W+1 :=
    (width_mono (by simpa only [Int.natAbs_natCast] using Nat.div_le_self (n+1) 2)).trans hsum
  have hcountN : (n+1)/2 ≤ n+1 := Nat.div_le_self _ _
  by_cases hpos : 0 < (n+1)/2
  all_goals
    simp only [initialM, BufferIndex.literal, BufferIndex.ofBytes, BufferIndex.repeatArray,
      BufferIndex.set, Index.add, Index.div, Index.binary, perform, MonadCost.emit,
      Bind.bind, Pure.pure, Generator.bind, Generator.yield]
    refine ⟨_,_,by
      iterate 6
        apply Returns.yield rfl
        apply Returns.skip rfl
      dsimp only
      simp only [size_mul,size_bytearray,PythonBytes.size_literal,Array.size_singleton,
        Nat.one_mul,hpos,↓reduceIte]
      repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,?_,?_,?_,?_⟩
    · constructor
      · change _ = if 0 < size ((bytearray (b[0x01]) : B)*((n+1)/2)) then _ else _
        simp only [size_mul,size_bytearray,PythonBytes.size_literal,Array.size_singleton,
          Nat.one_mul,hpos,↓reduceIte]
      · simp only [size_set!,size_mul,size_bytearray,PythonBytes.size_literal,Array.size_singleton,
          Nat.one_mul]
    · simp [hallowed]
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook,
        integerSchoolbook,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        PythonBytes.size_literal,Array.size_singleton,size_bytearray,Nat.one_mul]
      norm_num only [Nat.cast_ofNat,UInt8.toNat_ofNat',Nat.reduceMod]
      have h0 : width (0 : ℤ) = 1 := by decide
      have h1 : width (1 : ℤ) = 1 := by decide
      have h2 : width (2 : ℤ) = 2 := by decide
      simp only [h0,h1,h2]
      have hnw : width (n : ℤ) = W := rfl
      rw [hnw]
      have hsq : W ≤ W^2 := Nat.le_self_pow (by omega) W
      have hu0 : width (((0 : UInt8).toNat : ℕ) : ℤ) = 1 := by decide
      simp only [hu0,max_eq_left hw]
      change _ ≤ 32*(n+1+W^2)
      nlinarith only [hw,hsum,hcount,hcountN,hsq]
    · rfl

private theorem sieveM_id_fold (n : ℕ) : Id.run (sieveM (m := Id) B n) =
    (List.range' 3 ((n.sqrt+1-3+2-1)/2) 2).foldl
      (fun bytes p => Id.run (markM (m := Id) B p bytes)) (Id.run (initialM (m := Id) B n)) := by
  change Id.run (ForIn.forIn ([3:n.sqrt+1:2] : Std.Legacy.Range)
    (Id.run (initialM (m := Id) B n))
    (fun p bytes => ForInStep.yield <$> markM (m := Id) B p bytes)) = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_yield_eq_foldlM, List.idRun_foldlM]
  simp only [id_map']
  rfl

private theorem bound_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n : ℕ) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (do let x ← Index.sqrt n; Index.add x 1 : Generator.Computation (Event ⊕ ℕ) ℕ)
      (fun r => r = n.sqrt+1) (8*PrimeExponent.inputWidth n^2) 0 := by
  let W := PrimeExponent.inputWidth n
  have hw : 1 ≤ W := PrimeExponent.inputWidth_pos n
  have hs : width (n.sqrt : ℤ) ≤ W := width_mono (by simpa only [Int.natAbs_natCast] using Nat.sqrt_le_self n)
  have hs1 : width ((n.sqrt+1 : ℕ) : ℤ) ≤ W+1 := by
    have h := width_add (n.sqrt : ℤ) 1
    have h1 : width (1 : ℤ) = 1 := by decide
    rw [h1] at h
    simpa only [Nat.cast_add,Nat.cast_one] using h.trans (Nat.add_le_add_right (max_le hs hw) 1)
  simp only [Index.sqrt,Index.add,Index.binary,perform,MonadCost.emit,Bind.bind,Pure.pure,
    Generator.bind,Generator.yield]
  refine ⟨_,_,by repeat first | apply Returns.yield rfl | apply Returns.skip rfl | exact Returns.done _,rfl,?_,?_,?_⟩
  · simp [hallowed]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,traceWeight,schoolbook,integerSchoolbook,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    have h1 : width (1 : ℤ) = 1 := by decide
    norm_num only [Nat.cast_ofNat]
    rw [h1]
    change _ ≤ 8*W^2
    have hn : width (n : ℤ) = W := rfl
    rw [hn]
    have hm : max (width (n.sqrt : ℤ)) 1 ≤ W := max_le hs hw
    have hsquare : W ≤ W^2 := Nat.le_self_pow (by omega) W
    nlinarith only [hw,hs,hs1,hm,hsquare]
  · rfl


theorem sieve_budgeted (measure : ℕ → ℕ) (allowed : Event ⊕ ℕ → Prop)
    (hallowed : ∀ e, allowed (.inl e)) (price n : ℕ) :
    Budgeted (traceWeight price) (traceMeasure measure) allowed
      (sieveM (m := Generator.Computation (Event ⊕ ℕ)) B n)
      (fun r => r = Id.run (sieveM (m := Id) B n) ∧ size r = (n+1)/2)
      (128*(n+1)*(n+1+PrimeExponent.inputWidth n^2)) 0 := by
  let W := PrimeExponent.inputWidth n
  let T := n+1+W^2
  let xs := List.range' 3 ((n.sqrt+1-3+2-1)/2) 2
  have hlen : xs.length ≤ n+1 := by
    have h := Nat.sqrt_le_self n
    simp only [xs,List.length_range']
    omega
  have hvisit (p : ℕ) (hp : p ∈ xs) : 3 ≤ p ∧ p%2=1 ∧ p*p ≤ n := by
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hp
    have hupper : 3+2*j ≤ n.sqrt := by dsimp [xs] at hj; omega
    exact ⟨by omega, by omega, by simpa only [pow_two] using Nat.le_sqrt'.mp hupper⟩
  have hfor (bytes : B) (hb : size bytes = (n+1)/2) :
      Budgeted (traceWeight price) (traceMeasure measure) allowed
        (ForIn.forIn ([3:n.sqrt+1:2] : Std.Legacy.Range) bytes
          (fun p bytes => ForInStep.yield <$> markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes))
        (fun r => r = xs.foldl (fun bytes p => Id.run (markM (m := Id) B p bytes)) bytes ∧
          size r = (n+1)/2) (64*(n+1)*T) 0 := by
    have hfold := Generator.Budgeted.foldlM (weight := traceWeight price) (count := traceMeasure measure)
      xs (fun bytes p => markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes)
      (fun bytes p => Id.run (markM (m := Id) B p bytes)) (fun bytes => size bytes = (n+1)/2)
      (fun _ => 64*T) (fun _ => 0) (by
        intro bytes hb p hp
        have hv := hvisit p hp
        exact (mark_budgeted B measure allowed hallowed price n p bytes hb hv.1 hv.2.1 hv.2.2).mono
          (fun r hr => ⟨hr.1,hr.2.trans hb⟩) (le_refl _) (le_refl _)) bytes hb
    rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_yield_eq_foldlM]
    simp only [id_map']
    apply hfold.mono (fun _ h => h)
    · have hm := Nat.mul_le_mul_right (64*T) hlen
      simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm
    · simp
  have hi := initial_budgeted B measure allowed hallowed price n
  have hall := hi.bind
    (f := fun bytes => do
      let bound ← (do let x ← Index.sqrt n; Index.add x 1)
      ForIn.forIn ([3:bound:2] : Std.Legacy.Range) bytes
        (fun p bytes => ForInStep.yield <$> markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes))
    (post' := fun r => r = Id.run (sieveM (m := Id) B n) ∧ size r = (n+1)/2)
    (d := 8*W^2+64*(n+1)*T) (r := 0) (by
      intro bytes hb
      rcases hb with ⟨rfl,hb⟩
      apply (bound_budgeted measure allowed hallowed price n).bind
        (f := fun bound => ForIn.forIn ([3:bound:2] : Std.Legacy.Range) (Id.run (initialM (m := Id) B n))
          (fun p bytes => ForInStep.yield <$> markM (m := Generator.Computation (Event ⊕ ℕ)) B p bytes))
        (d := 64*(n+1)*T) (r := 0)
      intro bound hbound
      subst bound
      apply (hfor _ hb).mono
      · intro r hr
        refine ⟨?_,hr.2⟩
        rw [sieveM_id_fold B n]
        exact hr.1
      · rfl
      · rfl)
  have h : Budgeted (traceWeight price) (traceMeasure measure) allowed
      (sieveM (m := Generator.Computation (Event ⊕ ℕ)) B n)
      (fun r => r = Id.run (sieveM (m := Id) B n) ∧ size r = (n+1)/2)
      (32*T+(8*W^2+64*(n+1)*T)) 0 := by
    simpa only [sieveM,_root_.bind_pure,bind_pure_comp,Nat.zero_add] using hall
  apply h.mono (fun _ h => h) ?_ (le_refl _)
  have hT : T ≤ (n+1)*T := Nat.le_mul_of_pos_left _ (by omega)
  have hW : W^2 ≤ T := by dsimp [T]; omega
  change 32*T+(8*W^2+64*(n+1)*T) ≤ 128*(n+1)*T
  nlinarith only [hT,hW]

end SympyBinomial.ByteSieve
