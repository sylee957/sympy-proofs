module

public import SympyProofs.Binomial.Algorithms.ByteSieveGenerator
public import SympyProofs.Binomial.Basic
public import Mathlib.Data.List.Sort
public import SympyProofs.Python.Generator.Correctness

/-!
# Correctness of the monadic odd-prime generator

The table invariant proves primality at every byte. A finite interpreter trace
then proves termination and exact ordered enumeration directly, including
agreement of consuming loops with the mathematical prime list. The proof-only `search`
exposes the continuation saved by ordinary `do` notation.
-/

@[expose] public section

namespace SympyBinomial.ByteSieve

open PythonByteArray Generator Std Std.Iterators
open scoped Std.WP PythonBytes

variable (B : Type) [PythonByteArray B]

/-- Proof helper for the byte table built inline inside `oddPrimesGenerator`. -/
def sieve (limit : ℕ) : Value B := Id.run do
  let mut bytes : Value B := (bytearray (b[0x01]) : B) * ((limit + 1) / 2)
  if 0 < bytes.size then
    bytes := bytes.set! 0 0
  for hp : p in [3:limit.sqrt + 1:2] do
    if bytes[p / 2]! ≠ 0 then
      let start := p * p / 2
      let count := (bytes.len - 1 - (start : ℤ)).fdiv p + 1
      have hp_pos : 0 < p := by have h : 3 ≤ p := hp.lower; omega
      bytes := bytes.setSlice start p ((b[0x00] : Bytes B) * count)
        hp_pos (by simpa [count] using size_singleton_mul_sliceCount bytes 0 start p hp_pos)
  return bytes

theorem size_sieve (limit : ℕ) : (sieve B limit).size = (limit + 1) / 2 := by
  generalize he : sieve B limit = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun _ _ current => size current = (limit + 1) / 2
  · fun _ _ current => size current = (limit + 1) / 2
  all_goals simp_all +zetaDelta

private theorem odd_minFac {m : ℕ} (hm : m % 2 = 1) : m.minFac % 2 = 1 := by
  by_cases h : m = 1
  · simp [h]
  rcases (Nat.minFac_prime h).eq_two_or_odd with ht | ht
  · have hd := Nat.minFac_dvd m
    rw [ht] at hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  · exact ht

private theorem phase_at_self {p : ℕ} (hp : 3 ≤ p) :
    (p.Prime ∨ p ≤ p.minFac) ↔ p.Prime := by
  constructor
  · rintro (h | h)
    · exact h
    · exact Nat.prime_def_minFac.mpr ⟨by omega,
        Nat.le_antisymm (Nat.minFac_le (by omega)) h⟩
  · exact Or.inl

private theorem phase_skip {p m : ℕ} (hm : m % 2 = 1) (hp : p % 2 = 1)
    (hp3 : 3 ≤ p) (hnp : ¬p.Prime) :
    (m.Prime ∨ p + 2 ≤ m.minFac) ↔ (m.Prime ∨ p ≤ m.minFac) := by
  have hf := odd_minFac hm
  have hne : m.minFac ≠ p := by
    intro h
    have hm1 : m ≠ 1 := by intro he; simp [he] at h; omega
    exact hnp (h ▸ Nat.minFac_prime hm1)
  constructor <;> rintro (h | h)
  · exact Or.inl h
  · exact Or.inr (by omega)
  · exact Or.inl h
  · exact Or.inr (by omega)

private theorem phase_step {p m : ℕ} (hm : m % 2 = 1) (hp : p % 2 = 1)
    (hprime : p.Prime) :
    (m.Prime ∨ p + 2 ≤ m.minFac) ↔
      (m.Prime ∨ p ≤ m.minFac) ∧ ¬(p * p ≤ m ∧ p ∣ m) := by
  have hf := odd_minFac hm
  have hp2 := hprime.two_le
  have hm0 : 0 < m := by omega
  constructor
  · intro h
    refine ⟨h.imp_right (by omega), ?_⟩
    rintro ⟨hle, hd⟩
    rcases h with h | h
    · have he := (Nat.prime_dvd_prime_iff_eq hprime h).mp hd
      subst m
      nlinarith
    · have := Nat.minFac_le_of_dvd hp2 hd
      omega
  · rintro ⟨h, hn⟩
    rcases h with h | h
    · exact Or.inl h
    · by_cases hpr : m.Prime
      · exact Or.inl hpr
      · right
        have hne : m.minFac ≠ p := by
          intro he
          apply hn
          constructor
          · simpa [he, pow_two] using Nat.minFac_sq_le_self hm0 hpr
          · simpa [he] using Nat.minFac_dvd m
        omega

private theorem marked_iff {p i size : ℕ} (hp : p.Prime) (ho : p % 2 = 1)
    (hi : i < size) :
    i ∈ ForIn.toList (⟨p * p / 2, size, p, hp.pos⟩ : Std.Legacy.Range) ↔
      p * p ≤ 2 * i + 1 ∧ p ∣ 2 * i + 1 := by
  rw [Std.Internal.LawfulMemForInId.mem_toList_iff]
  change (p * p / 2 ≤ i ∧ i < size ∧ (i - p * p / 2)%p = 0) ↔ _
  have hs : 2 * (p * p / 2) + 1 = p * p := by
    have : (p * p)%2 = 1 := by simp [Nat.mul_mod, ho]
    omega
  have hdiv (hh : p * p / 2 ≤ i) : p ∣ i - p * p / 2 ↔ p ∣ 2 * i + 1 := by
    have he : 2 * i + 1 = p * p + 2 * (i - p * p / 2) := by omega
    rw [he, ← Nat.dvd_add_iff_right (dvd_mul_right p p), hp.dvd_mul]
    have hn : ¬p ∣ 2 := by
      intro hd
      have := (Nat.dvd_prime Nat.prime_two).mp hd
      have := hp.two_le
      omega
    simp [hn]
  constructor
  · rintro ⟨hh, _, hd⟩
    exact ⟨by omega, (hdiv hh).mp (Nat.dvd_of_mod_eq_zero hd)⟩
  · rintro ⟨hh, hd⟩
    have hh' : p * p / 2 ≤ i := by omega
    exact ⟨hh', hi, Nat.mod_eq_zero_of_dvd ((hdiv hh').mpr hd)⟩

private theorem get_initial (value : UInt8) (count i : ℕ) (hi : i < count) :
    getByte ((bytearray (b[value]) : B) * count) i = value := by
  change getByte (repeatBytes (bytearray (b[value]) : B) count) i = value
  rw [get_repeat (bytearray (b[value]) : B) count i (by simpa [size_repeat] using hi)]
  simp only [size_bytearray, PythonBytes.size_literal, Array.size_singleton, Nat.mod_one]
  rw [show bytearray (b[value]) = (ofBytes (b[value]) : B) from rfl,
    get_ofBytes _ _ (by simp), PythonBytes.get_literal _ _ (by simp)]
  rfl

private theorem get_zero_slice (bytes : B) (start step : ℕ) (hs : 0 < step)
    (j : ℕ) :
    getByte (setSlice bytes start step
      ((b[0] : Bytes B) * ((len bytes - 1 - start).fdiv step + 1)) hs
      (size_singleton_mul_sliceCount bytes 0 start step hs)) j =
      if j ∈ ForIn.toList (⟨start, size bytes, step, hs⟩ : Std.Legacy.Range)
      then 0 else getByte bytes j := by
  refine (get_setSlice bytes start step _ hs _ j).trans ?_
  split_ifs with hj
  · have hb := slice_index_lt bytes start step j hs hj
    have hr := size_singleton_mul_sliceCount bytes 0 start step hs
    rw [← hr] at hb
    change PythonBytes.getByte (PythonBytes.repeatBytes _ _) _ = 0
    rw [PythonBytes.get_repeat _ _ _ hb]
    simp only [PythonBytes.size_literal, Array.size_singleton, Nat.mod_one]
    rw [PythonBytes.get_literal _ _ (by simp)]
    rfl
  · rfl

private theorem range_index {limit p : ℕ} {pref suff : List ℕ}
    (h : ForIn.toList [3:limit.sqrt + 1:2] = pref ++ p :: suff) :
    p = 3 + 2 * pref.length := by
  have h' : List.range' 3 ((limit.sqrt + 1 - 3 + 2 - 1) / 2) 2 = pref ++ p :: suff :=
    by simpa using h
  obtain ⟨j, _, hp, ht⟩ := List.range'_eq_append_iff.mp h'
  rw [hp]
  have hh := List.range'_eq_cons_iff.mp ht.symm
  simp only [List.length_range']
  omega

/-- Every in-bounds byte is exactly the primality indicator of its odd number. -/
theorem sieve_spec (limit : ℕ) :
    ∀ i, i < (sieve B limit).size →
      getByte (sieve B limit) i = if Nat.Prime (2 * i + 1) then 1 else 0 := by
  generalize he : sieve B limit = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ current => size current = (limit + 1)/2 ∧
      ∀ i, i < size current → getByte current i =
        if Nat.Prime (2 * i + 1) ∨ 3 + 2 * pref.length ≤ (2 * i + 1).minFac then 1 else 0
  · fun pref _ current => size current = (limit + 1)/2 ∧
      ∀ i, i < size current → getByte current i =
        if Nat.Prime (2 * i + 1) ∨ 3 + 2 * pref.length ≤ (2 * i + 1).minFac then 1 else 0
  case vc1 =>
    rename_i old jp hpos
    refine ⟨by simp [bytes, old], ?_⟩
    intro i hi
    have hi' : i < (limit + 1)/2 := by simpa [bytes, old] using hi
    dsimp only [bytes]
    rw [get_set! _ _ _ hpos]
    by_cases hzero : i = 0
    · simp [hzero, Nat.not_prime_one]
    · rw [ite_eq_right (Ne.symm hzero), get_initial B _ _ _ hi']
      have hf := odd_minFac (m := 2 * i + 1) (by omega)
      have hf2 := (Nat.minFac_prime (show 2 * i + 1 ≠ 1 by omega)).two_le
      simp [show 3 ≤ (2 * i + 1).minFac by omega]
  case vc5 =>
    rename_i jp hempty
    exact ⟨by simp [bytes], fun i hi => False.elim (by omega)⟩
  case vc2 | vc6 =>
    rename_i current hinv i hi
    rw [hinv.2 i hi]
    have hstop : limit.sqrt < 3 + 2 * (ForIn.toList [3:limit.sqrt + 1:2]).length := by
      simp only [Std.Internal.ForIn.toList_range, List.length_range', Std.Legacy.Range.size]
      dsimp
      omega
    have hle : 2 * i + 1 ≤ limit := by omega
    by_cases hp : (2 * i + 1).Prime
    · simp [hp]
    · have hf := Nat.minFac_sq_le_self (show 0 < 2 * i + 1 by omega) hp
      have hs := Nat.le_sqrt'.mpr (hf.trans hle)
      simp only [hp, false_or, ite_false, show ¬3 + 2 * (ForIn.toList [3:limit.sqrt + 1:2]).length ≤
        (2 * i + 1).minFac by omega]
  case vc3 | vc7 =>
    rename_i pref p suff hs current hinv hnonzero
    have hpidx := range_index hs
    have hmem : p ∈ ([3:limit.sqrt + 1:2] : Std.Legacy.Range) :=
      Std.Internal.LawfulMemForInId.mem_toList_iff.mp (hs ▸ List.mem_append_right _ (by simp))
    have hp3 : 3 ≤ p := hmem.1
    have hpo : p % 2 = 1 := by omega
    have hpi : p / 2 < size current := by
      have := Nat.sqrt_le_self limit
      have : p < limit.sqrt + 1 := hmem.2.1
      omega
    have hv := hinv.2 (p / 2) hpi
    have hrepr : 2 * (p / 2) + 1 = p := by omega
    rw [hrepr, ← hpidx] at hv
    simp only [phase_at_self hp3] at hv
    rw [getElem!_eq_getByte _ _ hpi, hv] at hnonzero
    have hprime : p.Prime := by simpa using hnonzero
    have hsize : size bytes = size current := size_setSlice _ _ _ _ _ _
    refine ⟨hsize.trans hinv.1, ?_⟩
    intro i hi
    have hi' : i < size current := by omega
    dsimp only [bytes, start, count]
    rw [get_zero_slice B]
    simp only [marked_iff hprime hpo hi', hinv.2 i hi']
    have hstep := phase_step (m := 2 * i + 1) (by omega) hpo hprime
    simp only [List.length_append, List.length_singleton]
    rw [show 3 + 2 * (pref.length + 1) = p + 2 by omega, ← hpidx]
    simp only [hstep]
    split_ifs <;> simp_all; omega
  case vc4 | vc8 =>
    rename_i pref p suff hs current hinv hzero
    have hpidx := range_index hs
    have hmem : p ∈ ([3:limit.sqrt + 1:2] : Std.Legacy.Range) :=
      Std.Internal.LawfulMemForInId.mem_toList_iff.mp (hs ▸ List.mem_append_right _ (by simp))
    have hp3 : 3 ≤ p := hmem.1
    have hpo : p % 2 = 1 := by omega
    have hpi : p / 2 < size current := by
      have := Nat.sqrt_le_self limit
      have : p < limit.sqrt + 1 := hmem.2.1
      omega
    have hv := hinv.2 (p / 2) hpi
    have hrepr : 2 * (p / 2) + 1 = p := by omega
    rw [hrepr, ← hpidx] at hv
    simp only [phase_at_self hp3] at hv
    rw [getElem!_eq_getByte _ _ hpi, hv] at hzero
    have hnp : ¬p.Prime := by simpa using hzero
    refine ⟨hinv.1, ?_⟩
    intro i hi
    rw [hinv.2 i hi]
    simp only [List.length_append, List.length_singleton]
    rw [show 3 + 2 * (pref.length + 1) = p + 2 by omega, ← hpidx]
    simp only [phase_skip (m := 2 * i + 1) (by omega) hpo hp3 hnp]

/-- Marked slots correspond exactly to the increasing list of odd primes. -/
private theorem sieve_slots_eq_primes (limit : ℕ) :
    (((List.range (size (sieve B limit))).filter
      (fun j => getByte (sieve B limit) j == 1)).map (fun j => 2 * j + 1)) =
      (List.range (limit + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2)) := by
  have hsize : size (sieve B limit) = (limit + 1)/2 := size_sieve B limit
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_range.filter _).map _ (by intros; omega)
  · exact List.pairwise_lt_range.filter _
  · intro p
    simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨hi, hv⟩, rfl⟩
      have hprime : (2 * i + 1).Prime := by
        rw [sieve_spec B limit i hi] at hv
        split_ifs at hv with h
        · exact h
        · contradiction
      rw [hsize] at hi
      exact ⟨by omega, hprime, by omega⟩
    · rintro ⟨hle, hp, hp2⟩
      have ho := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      have hi : p / 2 < size (sieve B limit) := by rw [hsize]; omega
      have he : 2 * (p / 2) + 1 = p := by omega
      refine ⟨p / 2, ⟨hi, ?_⟩, he⟩
      rw [sieve_spec B limit _ hi, he, ite_eq_left hp]

/-- Proof helper for one pass through the yielding loop. -/
def searchBody (bytes : B) (i : ℤ) : Generator.Computation ℕ (ForInStep ℤ) := do
  if i ≠ -1 then
    Generator.yield (2 * i.toNat + 1)
    return .yield (find bytes 0x01 (i.toNat + 1))
  else return .done i

/-- Proof helper exposing the search loop and its saved integer index. -/
def search (bytes : B) (i : ℤ) : Generator.Computation ℕ Unit :=
  .loop ℤ (searchBody B bytes) i (fun _ => .done ())

private theorem ite_yield {m : Type → Type u} [Pure m] {α : Type}
    (p : Prop) [Decidable p] (x y : α) :
    (if p then pure (ForInStep.yield x) else pure (ForInStep.yield y)) =
      (pure (ForInStep.yield (if p then x else y)) : m (ForInStep α)) := by
  split <;> rfl

/-- Before the first resume, initialization is still inside the deferred body. -/
theorem generator_initial (limit : ℕ) : oddPrimesGenerator B limit =
    Generator.create (fun () => search B (sieve B limit) (find (sieve B limit) 0x01 1)) := by
  simp only [oddPrimesGenerator, sieve, Id.run]
  split
  all_goals
    simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', ite_yield,
      List.forIn'_pure_yield_eq_foldl]
    rfl

private theorem search_step (bytes : B) (i : ℤ) :
    (search B bytes i).step = .skip (if i = -1 then .done () else
      .suspended (2 * i.toNat + 1)
        (fun () => search B bytes (find bytes 0x01 (i.toNat + 1)))) := by
  by_cases h : i = -1 <;>
    simp [search, searchBody, Computation.step, h, Bind.bind, Pure.pure,
      Generator.bind, Generator.yield]

private def slotsFrom (bytes : B) (start : ℕ) : List ℕ :=
  (List.range (size bytes)).filter (fun j => decide (start ≤ j) && getByte bytes j == 0x01)

private theorem mem_slotsFrom (bytes : B) (start j : ℕ) :
    j ∈ slotsFrom B bytes start ↔ j < size bytes ∧ start ≤ j ∧ getByte bytes j = 0x01 := by
  simp [slotsFrom]

private theorem slotsFrom_next (bytes : B) (start : ℕ) :
    slotsFrom B bytes start =
      if find bytes 0x01 start = -1 then []
      else (find bytes 0x01 start).toNat ::
        slotsFrom B bytes ((find bytes 0x01 start).toNat + 1) := by
  rcases find_spec bytes 0x01 start with hf | hf
  · rw [ite_eq_left hf.1]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    obtain ⟨hb, hs, hv⟩ := (mem_slotsFrom B bytes start j).mp hj
    exact hf.2 j hs hb hv
  · rw [ite_eq_right (by omega)]
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
    · exact List.pairwise_lt_range.filter _
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_lt_range.filter _⟩
      intro j hj
      have := (mem_slotsFrom B bytes _ j).mp hj
      omega
    · intro j
      simp only [mem_slotsFrom, List.mem_cons]
      constructor
      · rintro ⟨hb, hs, hv⟩
        by_cases he : j = (find bytes 0x01 start).toNat
        · exact Or.inl he
        · right
          refine ⟨hb, ?_, hv⟩
          by_contra hle
          exact hf.2.2.2.2 j hs (by omega) hv
      · rintro (rfl | ⟨hb, hs, hv⟩)
        · exact ⟨hf.2.2.1, hf.2.1, hf.2.2.2.1⟩
        · exact ⟨hb, by omega, hv⟩

private theorem search_produces (bytes : B) (start : ℕ) :
    Produces (search B bytes (find bytes 0x01 start))
      ((slotsFrom B bytes start).map (fun j => 2 * j + 1)) := by
  rw [slotsFrom_next]
  by_cases h : find bytes 0x01 start = -1
  · simp only [h, ↓reduceIte, List.map_nil]
    have hs := search_step B bytes (-1)
    simp only [↓reduceIte] at hs
    exact Produces.skip hs (Produces.done rfl)
  · simp only [h, ↓reduceIte, List.map_cons]
    have hs := search_step B bytes (find bytes 0x01 start)
    rw [ite_eq_right h] at hs
    apply Produces.skip hs
    apply Produces.yield rfl
    apply Produces.skip rfl
    exact search_produces bytes ((find bytes 0x01 start).toNat + 1)
termination_by size bytes + 1 - start
decreasing_by
  rcases find_spec bytes 0x01 start with hf | hf
  · exact (h hf.1).elim
  · omega

/-- The generator terminates after emitting exactly the increasing list of odd primes. -/
theorem oddPrimesGenerator_produces (limit : ℕ) :
    Produces (oddPrimesGenerator B limit)
      ((List.range (limit + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2))) := by
  have hstart : slotsFrom B (sieve B limit) 1 =
      (List.range (size (sieve B limit))).filter
        (fun j => getByte (sieve B limit) j == 1) := by
    apply List.filter_congr
    intro j hj
    have hb := List.mem_range.mp hj
    by_cases hzero : j = 0
    · subst j
      rw [sieve_spec B limit 0 hb]
      simp [Nat.not_prime_one]
    · simp [show 1 ≤ j by omega]
  rw [← sieve_slots_eq_primes B limit, ← hstart, generator_initial]
  exact Produces.skip rfl (search_produces B (sieve B limit) 1)

/-- All reachable continuations terminate, including the steps between yields. -/
instance (limit : ℕ) : Finite (Frame (oddPrimesGenerator B limit)) Id :=
  finite_of_halts (oddPrimesGenerator_produces B limit).halts

/-- All and only the odd primes up to `limit`, in increasing order. -/
theorem oddPrimesGenerator_spec (limit : ℕ) :
    (oddPrimesGenerator B limit).toList =
      (List.range (limit + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2)) :=
  (oddPrimesGenerator_produces B limit).toList

/-- Consuming the generator agrees with iterating over the mathematical prime list. -/
theorem oddPrimesGenerator_forIn {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (limit : ℕ) (initial : α) (body : ℕ → α → m (ForInStep α)) :
    ForIn.forIn (oddPrimesGenerator B limit) initial body =
      ForIn.forIn ((List.range (limit + 1)).filter (fun p => decide (p.Prime ∧ p ≠ 2)))
        initial body :=
  (oddPrimesGenerator_produces B limit).forIn initial body

end SympyBinomial.ByteSieve
