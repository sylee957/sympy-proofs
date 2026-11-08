module

public import SympyProofs.PythonSlice.Basic
public import Mathlib.Data.List.FinRange

import Init.Internal.Order.While

/-!
# Sampling an array of arbitrary length

A source `v : Fin n → α` has arbitrary finite length `n` and arbitrary contents.
`sample` normalizes a Python-style slice, runs a signed while loop, and reads
those source entries in order. Its definition does not use a ceiling formula.
`sampling_correspondence` identifies the result with the sign-based mathematical
progression and proves its length. Every read is proved to be in bounds.
The proof is split into `sampling_element` (the value at each position) and
`sampling_length` (the number of positions). `sample_eq_formula` reconstructs
whole-array equality from the element and size results using array extensionality.

`sample_while_eq_pmap` separately proves correctness by well-founded induction on
the distance to the exclusive stop, proving that every continuing step decreases it.
The cursor carries
an invariant bound as an erased proof; together with the stop comparison, it
provides the bounds needed for each array read.

The public sampling theorems take `first last stride : Option ℤ` separately.
Their hypothesis is `stride.getD 1 ≠ 0`: `none` defaults to one and `some 0`
is excluded. The `let A` and `let B` expressions show the omitted and explicit
bound cases directly; `last` is the exclusive stop.

With `δ(x) = (sign(x)^2 - sign(x))/2` and `p = δ(step)`, put
`C(x) = max(-p, min(n-p, x+n*δ(x)))`. Normalize explicit bounds with `C`;
omitted start and stop use `p*(n-1)` and `(1-p)*n-p` directly. Calling these
normalized bounds `A` and `B`, the theorem states:

```
L = max(0, ceil((B-A)/step))
sample(v, slice) = [v[A+k*step] for k in range(L)]
len(sample(v, slice)) = L
```

Division inside the ceiling is rational. `n` is universally quantified, not a
fixed numeric size. Empty sources and samples, either stride direction, and
repeated source values are all included. `sampleArray` gives the same operation
on a Lean `Array α`.

This is a mathematical model of Python slicing, not a verification of CPython
or SymPy implementation code. `sample` and `sampleArray` take no proof arguments.
The correspondence theorems assume nonzero stride; the executable model returns
`#[]` for zero stride rather than modeling Python's exception.
-/

@[expose] public section

namespace SympyProofs.PythonSlice

/-- Integer indexing for normalized slice positions, requiring both bounds. -/
local instance arrayIntGetElem {α : Type*} :
    GetElem (Array α) ℤ α (fun source i => 0 ≤ i ∧ i < source.size) where
  getElem source i hi := source[i.toNat]'(by omega)

/-- Executable slicing: resolve defaults and negative indices, clamp the start,
then read entries until the stop or the source boundary is reached.
Callers supply no proofs. Zero stride returns `#[]` as an invalid-case
convention; the Python correspondence theorems assume nonzero stride. -/
def sample {α : Type*} {n : ℕ} (v : Fin n → α)
    (first last stride : Option ℤ) : Array α := Id.run do
  let step : ℤ := if let some step := stride then step else 1
  if step = 0 then return #[]
  let source := Array.ofFn v
  if hp : 0 < step then
    let mut start : ℤ := if let some x := first then x else 0
    if start < 0 then
      start := start + n
    let mut stop : ℤ := if let some x := last then x else n
    if stop < 0 then
      stop := stop + n
    let mut i : {i : ℤ // 0 ≤ i} := ⟨max 0 start, by omega⟩
    let mut result : Array α := #[]
    while hi : i.val < min stop (n : ℤ) do
      have hindex : 0 ≤ i.val ∧ i.val < source.size := by
        have := i.property
        simp only [source, Array.size_ofFn]
        omega
      result := result.push (source[i.val]'hindex)
      i := ⟨i.val + step, by have := i.property; omega⟩
    return result
  else
    let mut start : ℤ := if let some x := first then x else (n : ℤ) - 1
    if start < 0 then
      start := start + n
    let mut stop : ℤ := if let some x := last then x else -1
    if last.isSome ∧ stop < 0 then
      stop := stop + n
    let mut i : {i : ℤ // i < n} := ⟨min ((n : ℤ) - 1) start, by omega⟩
    let mut result : Array α := #[]
    while hi : max stop (-1) < i.val do
      have hindex : 0 ≤ i.val ∧ i.val < source.size := by
        have := i.property
        simp only [source, Array.size_ofFn]
        omega
      result := result.push (source[i.val]'hindex)
      i := ⟨i.val + step, by have := i.property; omega⟩
    return result

/-- Concrete-array wrapper, also callable without proof arguments. -/
def sampleArray {α : Type*} (v : Array α) (r : RawSlice) : Array α :=
  sample (fun i : Fin v.size => v[i]) r.start r.stop r.step

/-- The executable model's convention for invalid zero stride. -/
theorem sample_zero_stride {α : Type*} {n : ℕ} (v : Fin n → α)
    (first last : Option ℤ) : sample v first last (some 0) = #[] := by
  rfl

/-- Equality of the operational slice range and its sign-based closed form.
The left side models `list(range(*slice(start, stop, step).indices(n)))` by
running the signed range loop on the normalized bounds. -/
theorem RawSlice.range_eq_formula (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    intRange (r.first n) (r.last n) r.stride hs =
      (List.range (r.dimensionBySign n).toNat).map
        (fun k : ℕ => r.firstBySign n + (k : ℤ) * r.stride) := by
  rw [intRange_eq_map_range, r.first_eq_sign n hs, r.last_eq_sign n hs]
  congr 2
  simp [RawSlice.dimensionBySign, length, ← Int.ceil_toNat]
  omega

theorem RawSlice.range_length_eq_formula (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    ((intRange (r.first n) (r.last n) r.stride hs).length : ℤ) = r.dimensionBySign n := by
  rw [intRange_length, r.first_eq_sign n hs, r.last_eq_sign n hs]
  rfl

/-- Every index emitted by the operational slice loop is a valid source index. -/
theorem RawSlice.range_bounds (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0)
    {i : ℤ} (hi : i ∈ intRange (r.first n) (r.last n) r.stride hs) :
    0 ≤ i ∧ i < n := by
  obtain ⟨k, hk, rfl⟩ := (mem_intRange hs).1 hi
  exact (continues_bounds (r.inBounds n) hs ((lt_length_iff hs).1 hk)).2

/-- A nonzero stride visits at most as many entries as the source contains. -/
theorem RawSlice.range_length_le (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (intRange (r.first n) (r.last n) r.stride hs).length ≤ n := by
  rw [intRange_eq_map_range, List.length_map, List.length_range]
  by_contra h
  have hk : n < length (r.first n) (r.last n) r.stride := by omega
  have hb := continues_bounds (r.inBounds n) hs ((lt_length_iff hs).1 hk)
  exact (Nat.lt_irrefl n) hb.1

private def sampleWhile {α : Type*} {n : ℕ} (v : Fin n → α)
    (inv guard : ℤ → Prop) [DecidablePred guard]
    (hg : ∀ i, inv i → guard i → i.toNat < n) (s : ℤ)
    (hstep : ∀ i, inv i → inv (i + s))
    (first : {i : ℤ // inv i}) (initial : Array α) : Array α := Id.run do
  let source := Array.ofFn v
  let mut i := first
  let mut result := initial
  while h : guard i.val do
    result := result.push (source[i.val.toNat]'(by
      simpa only [source, Array.size_ofFn] using hg i.val i.property h))
    i := ⟨i.val + s, hstep i.val i.property⟩
  return result

private theorem sampleWhile_eq {α : Type*} {n : ℕ} (v : Fin n → α)
    (inv guard : ℤ → Prop) [DecidablePred guard]
    (hg : ∀ i, inv i → guard i → i.toNat < n) (s : ℤ)
    (hstep : ∀ i, inv i → inv (i + s))
    (first : {i : ℤ // inv i}) (initial : Array α) :
    sampleWhile v inv guard hg s hstep first initial =
      if h : guard first.val then
        sampleWhile v inv guard hg s hstep ⟨first.val + s, hstep first.val first.property⟩
          (initial.push (v ⟨first.val.toNat, hg first.val first.property h⟩))
      else initial := by
  unfold sampleWhile
  change (Lean.Loop.forIn (m := Id) _ (first, initial) _).2 = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split <;> simp_all <;> rfl

/-- The cursor invariant is preserved on each update. Correctness and termination
follow by well-founded induction on the remaining distance to the stop. -/
private theorem sample_while_eq_pmap {α : Type*} {n : ℕ} (v : Fin n → α)
    (inv guard : ℤ → Prop) [DecidablePred guard]
    (hg : ∀ i, inv i → guard i → i.toNat < n) (last s : ℤ) (hs : s ≠ 0)
    (hstep : ∀ i, inv i → inv (i + s))
    (hstop : ∀ i, guard i → if 0 < s then i < last else last < i)
    (first : {i : ℤ // inv i}) (initial : Array α)
    (H : ∀ i ∈ intRange first.val last s hs, 0 ≤ i ∧ i < n)
    (Hguard : ∀ i ∈ intRange first.val last s hs, guard i) :
    (sampleWhile v inv guard hg s hstep first initial).toList = initial.toList ++
      (intRange first.val last s hs).pmap
        (fun (i : ℤ) (hi : 0 ≤ i ∧ i < n) => v ⟨i.toNat, by omega⟩) H := by
  rw [sampleWhile_eq]
  by_cases hc : (if 0 < s then first.val < last else last < first.val)
  · have hr : intRange first.val last s hs = first.val :: intRange (first.val + s) last s hs := by
      rw [intRange]
      exact dite_eq_left hc
    have hguard := Hguard first.val (by rw [hr]; exact List.mem_cons_self)
    rw [dite_eq_left hguard]
    rw [sample_while_eq_pmap v inv guard hg last s hs hstep hstop
      ⟨first.val + s, hstep first.val first.property⟩ _
      (fun i hi => H i (by rw [hr]; exact List.mem_cons_of_mem _ hi))
      (fun i hi => Hguard i (by rw [hr]; exact List.mem_cons_of_mem _ hi))]
    simp [hr, Array.toList_push, List.append_assoc]
  · have hguard : ¬guard first.val := fun h => hc (hstop first.val h)
    have hr : intRange first.val last s hs = [] := by
      rw [intRange]
      exact dite_eq_right hc
    simp [hguard, hr]
termination_by if 0 < s then (last - first.val).toNat else (first.val - last).toNat
decreasing_by split_ifs at * <;> omega

private theorem intRange_before_stop (a b s : ℤ) (hs : s ≠ 0) {i : ℤ}
    (hi : i ∈ intRange a b s hs) : if 0 < s then i < b else b < i := by
  obtain ⟨k, hk, rfl⟩ := (mem_intRange hs).mp hi
  exact (lt_length_iff hs).mp hk

/-- For positive strides, a start clipped only below and a stop limited by the
array boundary give the same range as fully clipped slice endpoints. -/
private theorem intRange_clamp_pos (n : ℕ) (f l s : ℤ) (hs : s ≠ 0) (hp : 0 < s) :
    intRange (max 0 f) (min l n) s hs =
      intRange (max 0 (min n f)) (max 0 (min n l)) s hs := by
  by_cases hc : max 0 f < min l (n : ℤ)
  · have ha : max 0 f = max 0 (min (n : ℤ) f) := by omega
    have hb : min l (n : ℤ) = max 0 (min (n : ℤ) l) := by omega
    exact congrArg₂ (fun a b => intRange a b s hs) ha hb
  · have hc' : ¬max 0 (min (n : ℤ) f) < max 0 (min (n : ℤ) l) := by omega
    conv_lhs => rw [intRange]; simp [hp, hc]
    rw [intRange]
    simp [hp, hc']

/-- For negative strides, a start clipped only above and a stop clipped only below
give the same range as fully clipped slice endpoints. -/
private theorem intRange_clamp_neg (n : ℕ) (f l s : ℤ) (hs : s ≠ 0) (hp : ¬0 < s) :
    intRange (min ((n : ℤ) - 1) f) (max l (-1)) s hs =
      intRange (max (-1) (min ((n : ℤ) - 1) f))
        (max (-1) (min ((n : ℤ) - 1) l)) s hs := by
  by_cases hc : max l (-1) < min ((n : ℤ) - 1) f
  · have ha : min ((n : ℤ) - 1) f = max (-1) (min ((n : ℤ) - 1) f) := by omega
    have hb : max l (-1) = max (-1) (min ((n : ℤ) - 1) l) := by omega
    exact congrArg₂ (fun a b => intRange a b s hs) ha hb
  · have hc' : ¬max (-1) (min ((n : ℤ) - 1) l) <
        max (-1) (min ((n : ℤ) - 1) f) := by omega
    conv_lhs => rw [intRange]; simp [hp, hc]
    rw [intRange]
    simp [hp, hc']

/-- Under nonzero stride, every operational read succeeds and the loop returns
exactly the values indexed by the normalized range. -/
theorem sample_eq_pmap {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    sample v r.start r.stop r.step =
      ((intRange (r.first n) (r.last n) r.stride hs).pmap
        (fun (i : ℤ) (hi : 0 ≤ i ∧ i < n) => v ⟨i.toNat, by omega⟩)
        (fun _ hi => r.range_bounds n hs hi)).toArray := by
  apply Array.ext'
  rw [List.toList_toArray]
  unfold sample
  extract_lets (onlyGivenNames := true) s source
  have hstep : s = r.stride := by
    dsimp [s, RawSlice.stride]
    cases r.step <;> rfl
  simp -zeta only [hstep, hs, ite_false]
  by_cases hp : 0 < r.stride
  · simp -zeta only [hp, dite_true]
    let f : ℤ := if let some x := r.start then
        if x < 0 then x + n else x
      else 0
    let l : ℤ := if let some x := r.stop then
        if x < 0 then x + n else x
      else n
    have hfirst : r.first n = max 0 (min (n : ℤ) f) := by
      cases hraw : r.start <;>
        simp [RawSlice.first, normalizeBound, hp, f, hraw]
    have hlast : r.last n = max 0 (min (n : ℤ) l) := by
      cases hraw : r.stop <;>
        simp [RawSlice.last, normalizeBound, hp, l, hraw]
    have hr : intRange (max 0 f) (min l n) r.stride hs =
        intRange (r.first n) (r.last n) r.stride hs := by
      rw [hfirst, hlast]
      exact intRange_clamp_pos n f l r.stride hs hp
    have H : ∀ i ∈ intRange (max 0 f) (min l n) r.stride hs, 0 ≤ i ∧ i < n := by
      intro i hi
      exact r.range_bounds n hs (hr ▸ hi)
    have h := sample_while_eq_pmap v (fun i => 0 ≤ i) (fun i => i < min l (n : ℤ))
      (fun i hinv hi => by omega) (min l n) r.stride hs
      (fun i hinv => by omega)
      (fun i hi => by simpa only [hp, ite_true] using hi) ⟨max 0 f, by omega⟩ #[] H
      (fun i hi => by
        simpa only [hp, ite_true] using intRange_before_stop _ _ _ hs hi)
    simp only [hr] at h
    simp [sampleWhile] at h ⊢
    convert h using 1
    cases hraw : r.start <;> cases hstop : r.stop <;>
      simp [f, l, hraw, hstop, source, hstep, Id.run, arrayIntGetElem] <;>
      (try split_ifs) <;> first | omega | congr 3
  · simp -zeta only [hp, dite_false]
    let f : ℤ := if let some x := r.start then
        if x < 0 then x + n else x
      else (n : ℤ) - 1
    let l : ℤ := if let some x := r.stop then
        if x < 0 then x + n else x
      else -1
    have hfirst : r.first n = max (-1) (min ((n : ℤ) - 1) f) := by
      cases hraw : r.start <;>
        simp [RawSlice.first, normalizeBound, hp, f, hraw]
    have hlast : r.last n = max (-1) (min ((n : ℤ) - 1) l) := by
      cases hraw : r.stop <;>
        simp [RawSlice.last, normalizeBound, hp, l, hraw]
    have hr : intRange (min ((n : ℤ) - 1) f) (max l (-1)) r.stride hs =
        intRange (r.first n) (r.last n) r.stride hs := by
      rw [hfirst, hlast]
      exact intRange_clamp_neg n f l r.stride hs hp
    have H : ∀ i ∈ intRange (min ((n : ℤ) - 1) f) (max l (-1)) r.stride hs,
        0 ≤ i ∧ i < n := by
      intro i hi
      exact r.range_bounds n hs (hr ▸ hi)
    have h := sample_while_eq_pmap v (fun i => i < (n : ℤ)) (fun i => max l (-1) < i)
      (fun i hinv hi => by omega) (max l (-1)) r.stride hs
      (fun i hinv => by omega)
      (fun i hi => by simpa only [hp, ite_false] using hi)
      ⟨min ((n : ℤ) - 1) f, by omega⟩ #[] H
      (fun i hi => by
        simpa only [hp, ite_false] using intRange_before_stop _ _ _ hs hi)
    simp only [hr] at h
    simp [sampleWhile] at h ⊢
    convert h using 1
    cases hraw : r.start <;> cases hstop : r.stop <;>
      simp [f, l, hraw, hstop, source, hstep, Id.run, arrayIntGetElem] <;>
      (try split_ifs) <;> first | omega | congr 3

theorem RawSlice.formulaLength_eq (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (r.dimensionBySign n).toNat = length (r.first n) (r.last n) r.stride := by
  rw [← r.dimension_eq_sign n hs]
  change (max 0 ⌈((r.last n : ℚ) - r.first n) / r.stride⌉).toNat = _
  rw [← length_eq_max_ceiling]
  simp

/-- The formula's affine indices are nonnegative and below the arbitrary source length. -/
theorem RawSlice.formula_bounds (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0)
    (k : Fin (r.dimensionBySign n).toNat) :
    0 ≤ r.firstBySign n + (k.val : ℤ) * r.stride ∧
      r.firstBySign n + (k.val : ℤ) * r.stride < n := by
  have hk : k.val < length (r.first n) (r.last n) r.stride := by
    simpa only [r.formulaLength_eq n hs] using k.isLt
  have h := (continues_bounds (r.inBounds n) hs ((lt_length_iff hs).1 hk)).2
  simpa only [r.first_eq_sign n hs] using h

/-- The mathematical source index, with bounds established independently of the contents. -/
def RawSlice.formulaIndex (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0)
    (k : Fin (r.dimensionBySign n).toNat) : Fin n :=
  ⟨(r.firstBySign n + (k.val : ℤ) * r.stride).toNat, by
    have := r.formula_bounds n hs k
    omega⟩

/-- Length proof: sampling preserves the operational range length, regardless of
source values. This proof does not use the element or whole-list equality theorem. -/
theorem sample_length {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    ((sample v r.start r.stop r.step).size : ℤ) = r.dimensionBySign n := by
  rw [sample_eq_pmap v r hs, List.size_toArray, List.length_pmap]
  exact r.range_length_eq_formula n hs

/-- Element proof: read the `k`th source index from the operational sample.
This proof does not use the whole-list equality theorem. -/
theorem sample_getElem {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) (k : Fin (r.dimensionBySign n).toNat) :
    (sample v r.start r.stop r.step)[k.val]? = some (v (r.formulaIndex n hs k)) := by
  simp only [sample_eq_pmap v r hs, List.getElem?_toArray,
    r.range_eq_formula n hs, List.pmap_map]
  rw [List.getElem?_eq_getElem (by simpa using k.isLt)]
  congr 1
  rw [List.getElem_pmap]
  simp [RawSlice.formulaIndex]

/-- Equal sizes and equal elements at each position give equality of arrays. -/
theorem sample_eq_formula {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    sample v r.start r.stop r.step = Array.ofFn (fun k => v (r.formulaIndex n hs k)) := by
  apply Array.ext
  · simp only [Array.size_ofFn]
    have h := sample_length v r hs
    omega
  · intro i hi hj
    have hk : i < (r.dimensionBySign n).toNat := by
      simpa only [Array.size_ofFn] using hj
    have h := sample_getElem v r hs ⟨i, hk⟩
    simpa only [Array.getElem?_eq_getElem hi, Option.some.injEq, Array.getElem_ofFn] using h

/-- Element membership, without assuming source values are distinct. -/
theorem mem_sample_iff {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) (x : α) :
    x ∈ sample v r.start r.stop r.step ↔ ∃ k, v (r.formulaIndex n hs k) = x := by
  rw [sample_eq_formula v r hs, Array.mem_ofFn]

/-- The element formula, expanded in full: every valid output position contains
the source value at `A + k * s`, where `s := stride.getD 1`.
`some` also asserts the element exists.
All three inputs are optional integers; omitted bounds use the defaults shown. -/
theorem sampling_element {α : Type*} (n : ℕ) (v : Fin n → α)
    (first last stride : Option ℤ) (hs : stride.getD 1 ≠ 0) :
    let s := stride.getD 1
    let δ := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let p := δ s
    let C := fun x : ℤ => max (-p) (min ((n : ℤ) - p) (x + (n : ℤ) * δ x))
    let A : ℤ := match first with
      | none => p * ((n : ℤ) - 1)
      | some x => C x
    let B : ℤ := match last with
      | none => (1 - p) * (n : ℤ) - p
      | some x => C x
    let L : ℤ := max 0 ⌈((B : ℚ) - A) / s⌉
    ∀ k : Fin L.toNat,
      let z : ℕ := (A + k.val * s).toNat
      let index : Fin n :=
        ⟨z, (RawSlice.formulaIndex { start := first, stop := last, step := stride } n hs k).isLt⟩
      (sample v first last stride)[k.val]? = some (v index) := by
  exact sample_getElem v { start := first, stop := last, step := stride } hs

/-- The length formula, expanded in full: the sample contains exactly `L` entries. -/
theorem sampling_length {α : Type*} (n : ℕ) (v : Fin n → α)
    (first last stride : Option ℤ) (hs : stride.getD 1 ≠ 0) :
    let s := stride.getD 1
    let δ := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let p := δ s
    let C := fun x : ℤ => max (-p) (min ((n : ℤ) - p) (x + (n : ℤ) * δ x))
    let A : ℤ := match first with
      | none => p * ((n : ℤ) - 1)
      | some x => C x
    let B : ℤ := match last with
      | none => (1 - p) * (n : ℤ) - p
      | some x => C x
    let L : ℤ := max 0 ⌈((B : ℚ) - A) / s⌉
    ((sample v first last stride).size : ℤ) = L := by
  exact sample_length v { start := first, stop := last, step := stride } hs

/-- Complete array-sampling correspondence, combining the element and length proofs.
The array equality follows from `sample_getElem` and `sample_length`;
`sampling_element` and `sampling_length` expose each result separately with the
same expanded formula. Each `Fin` proof certifies that the source read is in bounds. -/
theorem sampling_correspondence {α : Type*} (n : ℕ) (v : Fin n → α)
    (first last stride : Option ℤ) (hs : stride.getD 1 ≠ 0) :
    let s := stride.getD 1
    let δ := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let p := δ s
    let C := fun x : ℤ => max (-p) (min ((n : ℤ) - p) (x + (n : ℤ) * δ x))
    let A : ℤ := match first with
      | none => p * ((n : ℤ) - 1)
      | some x => C x
    let B : ℤ := match last with
      | none => (1 - p) * (n : ℤ) - p
      | some x => C x
    let L : ℤ := max 0 ⌈((B : ℚ) - A) / s⌉
    sample v first last stride = Array.ofFn (fun k : Fin L.toNat =>
      let z : ℕ := (A + k.val * s).toNat
      let index : Fin n :=
        ⟨z, (RawSlice.formulaIndex { start := first, stop := last, step := stride } n hs k).isLt⟩
      v index) ∧
      ((sample v first last stride).size : ℤ) = L := by
  exact ⟨sample_eq_formula v { start := first, stop := last, step := stride } hs,
    sampling_length n v first last stride hs⟩

/-- The concrete array has the same ordered entries and the same length formula. -/
theorem sampleArray_eq_formula {α : Type*} (v : Array α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    sampleArray v r =
      Array.ofFn (fun k => v[r.formulaIndex v.size hs k]) ∧
      ((sampleArray v r).size : ℤ) = r.dimensionBySign v.size := by
  constructor
  · exact sample_eq_formula (fun i : Fin v.size => v[i]) r hs
  · exact sample_length (fun i : Fin v.size => v[i]) r hs

end SympyProofs.PythonSlice
