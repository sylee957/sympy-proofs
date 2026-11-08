module

public import SympyProofs.PythonSlice.Sampling

/-!
# Slice bounds safe to pass through normalization again

For a normalized range bound `x`, store `E(n,x) = x - n * δ(x)`, where
`δ(x) = (sign(x)^2 - sign(x))/2`. In particular, the reverse boundary `-1`
is stored as `-n-1`, which Python normalizes back to `-1`.

`RawSlice.canonical` stores `(E(n,A), E(n,B), s)`, with `A,B,s` given by the
existing normalization formulas. Its `CanonicalSlice` result has integer fields
with no optional values. It preserves sampling and is idempotent when passed
back as explicit raw arguments using `CanonicalSlice.toRawSlice`.
These are canonical *raw slice* bounds, not the bounds of the resulting range.
Decode them with `D(n,x) = x + n * δ(x)` before computing `A + k*s` or
`max(0, ceil((B-A)/s))`. Both formulas and proofs include `n = 0`.
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

private theorem RawSlice.sign_bounds (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    -((r.stride.sign ^ 2 - r.stride.sign) / 2) ≤ r.firstBySign n ∧
      r.firstBySign n ≤ (n : ℤ) - (r.stride.sign ^ 2 - r.stride.sign) / 2 ∧
      -((r.stride.sign ^ 2 - r.stride.sign) / 2) ≤ r.lastBySign n ∧
      r.lastBySign n ≤ (n : ℤ) - (r.stride.sign ^ 2 - r.stride.sign) / 2 := by
  have hb := r.inBounds n
  rw [r.first_eq_sign n hs, r.last_eq_sign n hs] at hb
  by_cases hp : 0 < r.stride
  · have hn : ¬r.stride < 0 := by omega
    simpa [InBounds, hp, sign_indicator_eq_if, hn] using hb
  · have hn : r.stride < 0 := by omega
    simp only [InBounds, hp, ite_false] at hb
    simp only [sign_indicator_eq_if, hn, ite_true]
    omega

/-- Fully specified encoded slice arguments; all omissions have been resolved. -/
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
  let mut start : ℤ := p * ((n : ℤ) - 1)
  if let some x := r.start then
    start := x + (n : ℤ) * ((x.sign ^ 2 - x.sign) / 2)
    start := max (-p) (min ((n : ℤ) - p) start)
  let mut stop : ℤ := (1 - p) * (n : ℤ) - p
  if let some x := r.stop then
    stop := x + (n : ℤ) * ((x.sign ^ 2 - x.sign) / 2)
    stop := max (-p) (min ((n : ℤ) - p) stop)
  start := start - (n : ℤ) * ((start.sign ^ 2 - start.sign) / 2)
  stop := stop - (n : ℤ) * ((stop.sign ^ 2 - stop.sign) / 2)
  return { start, stop, step }

/-- The sequential computation agrees with the normalized and encoded formulas. -/
theorem RawSlice.canonical_eq_formula (r : RawSlice) (n : ℕ) :
    r.canonical n =
      { start := encodeBound n (r.firstBySign n)
        stop := encodeBound n (r.lastBySign n)
        step := r.stride } := by
  rcases r with ⟨start, stop, step⟩
  cases start <;> cases stop <;> rfl

@[simp] theorem RawSlice.canonical_step (r : RawSlice) (n : ℕ) :
    (r.canonical n).step = r.stride := by
  rw [r.canonical_eq_formula n]

@[simp] theorem RawSlice.canonical_first (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (r.canonical n).toRawSlice.firstBySign n = r.firstBySign n := by
  rw [r.canonical_eq_formula n]
  change normalizeBySign n r.stride (encodeBound n (r.firstBySign n)) = _
  have hb := r.sign_bounds n hs
  exact normalizeBySign_encodeBound n r.stride _ ⟨hb.1, hb.2.1⟩

@[simp] theorem RawSlice.canonical_last (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (r.canonical n).toRawSlice.lastBySign n = r.lastBySign n := by
  rw [r.canonical_eq_formula n]
  change normalizeBySign n r.stride (encodeBound n (r.lastBySign n)) = _
  have hb := r.sign_bounds n hs
  exact normalizeBySign_encodeBound n r.stride _ hb.2.2

/-- Rebuilding canonical raw arguments preserves the complete stored triple. -/
theorem RawSlice.canonical_idempotent (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (r.canonical n).toRawSlice.canonical n = r.canonical n := by
  rw [canonical_eq_formula, r.canonical_first n hs, r.canonical_last n hs,
    CanonicalSlice.toRawSlice_stride, canonical_step]
  exact (r.canonical_eq_formula n).symm

@[simp] theorem RawSlice.canonical_dimension (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    (r.canonical n).toRawSlice.dimensionBySign n = r.dimensionBySign n := by
  simp only [dimensionBySign, r.canonical_first n hs, r.canonical_last n hs,
    CanonicalSlice.toRawSlice_stride, canonical_step]

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
      r.canonical_first n hs, r.first_eq_sign n hs]
  have hb : (r.canonical n).toRawSlice.last n = r.last n := by
    rw [(r.canonical n).toRawSlice.last_eq_sign n hc,
      r.canonical_last n hs, r.last_eq_sign n hs]
  change sample v (r.canonical n).toRawSlice.start (r.canonical n).toRawSlice.stop
    (r.canonical n).toRawSlice.step = sample v r.start r.stop r.step
  rw [sample_eq_pmap v (r.canonical n).toRawSlice hc, sample_eq_pmap v r hs]
  simp only [ha, hb, CanonicalSlice.toRawSlice_stride, RawSlice.canonical_step]

/-- Length uses decoded bounds, not the stored sentinel `-n-1`. -/
theorem sampling_canonical_length {α : Type*} (n : ℕ) (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    let c := r.canonical n
    let A : ℤ := c.start + (n : ℤ) * ((c.start.sign ^ 2 - c.start.sign) / 2)
    let B : ℤ := c.stop + (n : ℤ) * ((c.stop.sign ^ 2 - c.stop.sign) / 2)
    ((sample v r.start r.stop r.step).size : ℤ) = max 0 ⌈((B : ℚ) - A) / c.step⌉ := by
  rw [r.canonical_eq_formula n]
  dsimp only
  rw [decode_encodeBound, decode_encodeBound]
  exact sample_length v r hs

/-- Decode the canonical bounds to recover each affine source index and its bounds. -/
theorem sampling_canonical_element {α : Type*} (n : ℕ) (v : Fin n → α)
    (r : RawSlice) (hs : r.stride ≠ 0) :
    let c := r.canonical n
    let A : ℤ := c.start + (n : ℤ) * ((c.start.sign ^ 2 - c.start.sign) / 2)
    let B : ℤ := c.stop + (n : ℤ) * ((c.stop.sign ^ 2 - c.stop.sign) / 2)
    let s := c.step
    let L : ℤ := max 0 ⌈((B : ℚ) - A) / s⌉
    ∀ k : Fin L.toNat,
      let i := A + (k.val : ℤ) * s
      (0 ≤ i ∧ i < n) ∧
        (sample v r.start r.stop r.step)[k.val]? = (Array.ofFn v)[i.toNat]? := by
  rw [r.canonical_eq_formula n]
  dsimp only
  intro k
  let k' : Fin (r.dimensionBySign n).toNat := ⟨k.val, by
    simpa only [decode_encodeBound, RawSlice.dimensionBySign] using k.isLt⟩
  simp only [decode_encodeBound]
  refine ⟨r.formula_bounds n hs k', ?_⟩
  rw [sample_getElem v r hs k']
  let index := r.formulaIndex n hs k'
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
