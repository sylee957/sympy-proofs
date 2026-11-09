module

public import SympyProofs.PythonSlice.Sampling

/-!
# Slice arguments with explicit defaults

`RawSlice.canonical` resolves omitted arguments and preserves every supplied
integer. With `s = step.getD 1` and `p = (sign(s)^2 - sign(s))/2`, the defaults
are `p*(n-1)` for start and `n-p*(2*n+1)` for stop. In particular, an omitted
reverse stop becomes the raw bound `-n-1`, which normalizes to `-1`.

This is an idempotent representation of raw arguments, not a unique triple for
every equivalent slice. Computing elements and lengths still requires relative
index adjustment and clipping. The sampling theorems display that complete
formula and include `n = 0`. Composition uses `encodeBound` to turn its computed
range endpoints into reusable raw arguments.
-/

@[expose] public section

namespace SympyProofs.PythonSlice

def encodeBound (n : ℕ) (x : ℤ) : ℤ := x - n * ((x.sign ^ 2 - x.sign) / 2)

/-- Decoding an encoded bound recovers it exactly, including negative sentinels. -/
theorem decode_encodeBound (n : ℕ) (x : ℤ) :
    encodeBound n x + (n : ℤ) *
      (((encodeBound n x).sign ^ 2 - (encodeBound n x).sign) / 2) = x := by
  by_cases hx : x < 0
  · have hneg : x - (n : ℤ) < 0 := by omega
    simp [encodeBound, sign_indicator_eq_if, hx, hneg]
  · simp [encodeBound, sign_indicator_eq_if, hx]

theorem normalizeBySign_encodeBound (n : ℕ) (s x : ℤ)
    (h : -((s.sign ^ 2 - s.sign) / 2) ≤ x ∧
      x ≤ (n : ℤ) - (s.sign ^ 2 - s.sign) / 2) :
    normalizeBySign n s (encodeBound n x) = x := by
  rw [normalizeBySign, decode_encodeBound, min_eq_right h.2, max_eq_right h.1]

/-- Fully specified raw slice arguments; all omissions have been resolved. -/
structure CanonicalSlice where
  start : ℤ
  stop : ℤ
  step : ℤ

/-- Pass the stored integers back to an interface accepting optional raw arguments. -/
def CanonicalSlice.toRawSlice (c : CanonicalSlice) : RawSlice :=
  { start := some c.start, stop := some c.stop, step := some c.step }

@[simp] theorem CanonicalSlice.toRawSlice_stride (c : CanonicalSlice) :
    c.toRawSlice.stride = c.step := rfl

def RawSlice.canonical (r : RawSlice) (n : ℕ) : CanonicalSlice := Id.run do
  let step := r.step.getD 1
  let p := (step.sign ^ 2 - step.sign) / 2
  let start := if let some x := r.start then x else p * ((n : ℤ) - 1)
  let stop := if let some x := r.stop then x else (n : ℤ) - p * (2 * n + 1)
  return { start, stop, step }

/-- Only omitted arguments are replaced by sign-dependent defaults. -/
theorem RawSlice.canonical_eq_formula (r : RawSlice) (n : ℕ) :
    let p := (r.stride.sign ^ 2 - r.stride.sign) / 2
    r.canonical n =
      { start := r.start.getD (p * ((n : ℤ) - 1))
        stop := r.stop.getD ((n : ℤ) - p * (2 * n + 1))
        step := r.stride } := by
  rcases r with ⟨start, stop, step⟩
  cases start <;> cases stop <;> rfl

@[simp] theorem RawSlice.canonical_step (r : RawSlice) (n : ℕ) :
    (r.canonical n).step = r.stride := by
  rw [r.canonical_eq_formula n]

@[simp] theorem RawSlice.canonical_start_of_some (r : RawSlice) (n : ℕ)
    {x : ℤ} (h : r.start = some x) : (r.canonical n).start = x := by
  simp [canonical_eq_formula, h]

@[simp] theorem RawSlice.canonical_stop_of_some (r : RawSlice) (n : ℕ)
    {x : ℤ} (h : r.stop = some x) : (r.canonical n).stop = x := by
  simp [canonical_eq_formula, h]

/-- Every fully explicit triple is fixed, even when its bounds lie outside the source. -/
@[simp] theorem CanonicalSlice.toRawSlice_canonical (c : CanonicalSlice) (n : ℕ) :
    c.toRawSlice.canonical n = c := by
  cases c
  rfl

@[simp] theorem RawSlice.canonical_first (r : RawSlice) (n : ℕ) :
    (r.canonical n).toRawSlice.firstBySign n = r.firstBySign n := by
  rw [r.canonical_eq_formula n]
  cases h : r.start with
  | some x => simp [CanonicalSlice.toRawSlice, firstBySign, stride, h]
  | none =>
    simp only [CanonicalSlice.toRawSlice, firstBySign, stride, Option.getD_some, h,
      Option.getD_none]
    simp only [normalizeBySign, sign_indicator_eq_if]
    split_ifs <;> omega

@[simp] theorem RawSlice.canonical_last (r : RawSlice) (n : ℕ) :
    (r.canonical n).toRawSlice.lastBySign n = r.lastBySign n := by
  rw [r.canonical_eq_formula n]
  cases h : r.stop with
  | some x => simp [CanonicalSlice.toRawSlice, lastBySign, stride, h]
  | none =>
    simp only [CanonicalSlice.toRawSlice, lastBySign, stride, Option.getD_some, h,
      Option.getD_none]
    simp only [normalizeBySign, sign_indicator_eq_if]
    split_ifs <;> omega

/-- Rebuilding canonical raw arguments preserves the complete stored triple. -/
theorem RawSlice.canonical_idempotent (r : RawSlice) (n : ℕ) :
    (r.canonical n).toRawSlice.canonical n = r.canonical n := by
  exact CanonicalSlice.toRawSlice_canonical _ n

@[simp] theorem RawSlice.canonical_dimension (r : RawSlice) (n : ℕ) :
    (r.canonical n).toRawSlice.dimensionBySign n = r.dimensionBySign n := by
  simp only [dimensionBySign, r.canonical_first n, r.canonical_last n,
    CanonicalSlice.toRawSlice_stride, canonical_step]

/-- Resolving defaults preserves the ordered range of source indices. -/
theorem RawSlice.canonical_range (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    intRange ((r.canonical n).toRawSlice.first n) ((r.canonical n).toRawSlice.last n)
      (r.canonical n).toRawSlice.stride (by simpa using hs) =
      intRange (r.first n) (r.last n) r.stride hs := by
  have hc : (r.canonical n).toRawSlice.stride ≠ 0 := by simpa using hs
  simp only [RawSlice.first_eq_sign _ n hc, RawSlice.last_eq_sign _ n hc,
    r.canonical_first n, r.canonical_last n,
    CanonicalSlice.toRawSlice_stride, RawSlice.canonical_step,
    r.first_eq_sign n hs, r.last_eq_sign n hs]

/-- Canonical raw arguments produce exactly the same ordered source entries. -/
theorem sample_canonical {α : Type*} {n : ℕ} (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    let c := r.canonical n
    sample v (some c.start) (some c.stop) (some c.step) =
      sample v r.start r.stop r.step := by
  have hc : (r.canonical n).toRawSlice.stride ≠ 0 := by
    simpa only [CanonicalSlice.toRawSlice_stride, r.canonical_step n] using hs
  have ha : (r.canonical n).toRawSlice.first n = r.first n := by
    rw [(r.canonical n).toRawSlice.first_eq_sign n hc,
      r.canonical_first n, r.first_eq_sign n hs]
  have hb : (r.canonical n).toRawSlice.last n = r.last n := by
    rw [(r.canonical n).toRawSlice.last_eq_sign n hc,
      r.canonical_last n, r.last_eq_sign n hs]
  change sample v (r.canonical n).toRawSlice.start (r.canonical n).toRawSlice.stop
    (r.canonical n).toRawSlice.step = sample v r.start r.stop r.step
  rw [sample_eq_pmap v (r.canonical n).toRawSlice hc, sample_eq_pmap v r hs]
  simp only [ha, hb, CanonicalSlice.toRawSlice_stride, RawSlice.canonical_step]

/-- Length uses relative-index adjustment and clipping of the stored raw bounds. -/
theorem sampling_canonical_length {α : Type*} (n : ℕ) (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    let c := r.canonical n
    let s := c.step
    let δ := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let p := δ s
    let C := fun x : ℤ => max (-p) (min ((n : ℤ) - p) (x + (n : ℤ) * δ x))
    let A := C c.start
    let B := C c.stop
    ((sample v r.start r.stop r.step).size : ℤ) = max 0 ⌈((B : ℚ) - A) / s⌉ := by
  dsimp only
  change ((sample v r.start r.stop r.step).size : ℤ) =
    (r.canonical n).toRawSlice.dimensionBySign n
  rw [r.canonical_dimension n]
  exact sample_length v r hs

/-- Normalize the stored raw bounds to recover each affine source index and its bounds. -/
theorem sampling_canonical_element {α : Type*} (n : ℕ) (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    let c := r.canonical n
    let s := c.step
    let δ := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let p := δ s
    let C := fun x : ℤ => max (-p) (min ((n : ℤ) - p) (x + (n : ℤ) * δ x))
    let A := C c.start
    let B := C c.stop
    let L : ℤ := max 0 ⌈((B : ℚ) - A) / s⌉
    ∀ k : Fin L.toNat,
      let i := A + (k.val : ℤ) * s
      (0 ≤ i ∧ i < n) ∧
        (sample v r.start r.stop r.step)[k.val]? = (Array.ofFn v)[i.toNat]? := by
  dsimp only
  change ∀ k : Fin ((r.canonical n).toRawSlice.dimensionBySign n).toNat,
    let i := (r.canonical n).toRawSlice.firstBySign n +
      (k.val : ℤ) * (r.canonical n).toRawSlice.stride
    (0 ≤ i ∧ i < n) ∧
      (sample v r.start r.stop r.step)[k.val]? = (Array.ofFn v)[i.toNat]?
  rw [r.canonical_dimension n]
  simp only [r.canonical_first n, CanonicalSlice.toRawSlice_stride, RawSlice.canonical_step]
  intro k
  refine ⟨r.formula_bounds n hs k, ?_⟩
  rw [sample_getElem v r hs k]
  let index := r.formulaIndex n hs k
  change some (v index) = (Array.ofFn v)[index.val]?
  simp [index.isLt]

/-- For every positive source length, some valid slice changes length when its
normalized bounds are reused as raw arguments. -/
theorem exists_renormalization_changes_length (n : ℕ) (hn : 0 < n) :
    ∃ r : RawSlice, r.stride ≠ 0 ∧
      let rebuilt : RawSlice :=
        { start := some (r.firstBySign n), stop := some (r.lastBySign n), step := r.step }
      r.dimensionBySign n ≠ rebuilt.dimensionBySign n := by
  let r : RawSlice := { step := some (-1) }
  refine ⟨r, by decide, ?_⟩
  have hnonneg : ¬(n : ℤ) - 1 < 0 := by omega
  have hstart : normalizeBySign n (-1) ((n : ℤ) - 1) = (n : ℤ) - 1 := by
    simp [normalizeBySign, sign_indicator_eq_if, hnonneg]
  have hstop : normalizeBySign n (-1) (-1) = (n : ℤ) - 1 := by
    norm_num [normalizeBySign, sign_indicator_eq_if]
  have hlength : r.dimensionBySign n = n := by
    norm_num [r, RawSlice.dimensionBySign, RawSlice.firstBySign, RawSlice.lastBySign,
      RawSlice.stride]
    rw [show (-1 - ((n : ℚ) - 1)) / -1 = (n : ℚ) by ring]
    simp
  dsimp only
  rw [hlength]
  simp [r, RawSlice.dimensionBySign, RawSlice.firstBySign, RawSlice.lastBySign,
    RawSlice.stride, hstart, hstop, Nat.ne_of_gt hn]

end SympyProofs.PythonSlice
