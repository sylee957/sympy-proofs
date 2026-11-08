module

public import SympyProofs.PythonSlice.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Python slice normalization for an arbitrary source length

`RawSlice` models optional integer start, stop and step. Negative explicit bounds
are relative to `n`, then clipped. Positive steps use bounds in `[0, n]` and
defaults `(0, n)`; negative steps use `[-1, n-1]` and defaults `(n-1, -1)`.
Defaults are used directly: an omitted reverse stop differs from explicit `-1`.
An omitted step means one; zero steps are outside the correctness hypotheses.

The sign-based formulas are proved equal to this normalization. The source
length `n : ℕ` is arbitrary, including zero. See `PythonSlice/Sampling.lean`
for the operational sampling theorem on values.

References:
* https://docs.python.org/3/library/stdtypes.html#common-sequence-operations
* https://docs.python.org/3/c-api/slice.html
-/

@[expose] public section

namespace SympyProofs.PythonSlice

/-- Normalized endpoints may be unordered. The allowed endpoint range depends on direction. -/
def InBounds (n : ℕ) (a b s : ℤ) : Prop :=
  if 0 < s then 0 ≤ a ∧ a ≤ n ∧ 0 ≤ b ∧ b ≤ n
  else -1 ≤ a ∧ a < n ∧ -1 ≤ b ∧ b < n

/-- A valid progression ordinal is below the parent dimension and selects an in-bounds index. -/
theorem continues_bounds {n : ℕ} {a b s : ℤ} {k : ℕ}
    (hb : InBounds n a b s) (hs : s ≠ 0) (hk : continues a b s k) :
    k < n ∧ 0 ≤ a + (k : ℤ) * s ∧ a + (k : ℤ) * s < n := by
  have hk0 : (0 : ℤ) ≤ k := by positivity
  by_cases hp : 0 < s
  · simp only [InBounds, continues, hp, ite_true] at hb hk
    have hs1 : 1 ≤ s := by omega
    have hm : (k : ℤ) ≤ (k : ℤ) * s := by nlinarith
    constructor
    · exact_mod_cast (show (k : ℤ) < n by omega)
    · omega
  · simp only [InBounds, continues, hp, ite_false] at hb hk
    have hs1 : s ≤ -1 := by omega
    have hm : (k : ℤ) * s ≤ -(k : ℤ) := by nlinarith
    constructor
    · exact_mod_cast (show (k : ℤ) < n by omega)
    · omega

/-- An independent finite enumeration: test the stopping predicate, without using `length`. -/
def ordinals (n : ℕ) (a b s : ℤ) : Finset ℕ :=
  (Finset.range n).filter (continues a b s)

/-- No valid ordinal is lost by restricting the independent enumeration to `range n`. -/
theorem ordinals_eq_range {n : ℕ} {a b s : ℤ}
    (hb : InBounds n a b s) (hs : s ≠ 0) :
    ordinals n a b s = Finset.range (length a b s) := by
  ext k
  simp only [ordinals, Finset.mem_filter, Finset.mem_range, lt_length_iff hs]
  exact ⟨And.right, fun hk => ⟨(continues_bounds hb hs hk).1, hk⟩⟩

/-- The selected parent indices, defined independently of the ceiling formula. -/
def indices (n : ℕ) (a b s : ℤ) : Finset ℤ :=
  (ordinals n a b s).image fun k : ℕ => a + (k : ℤ) * s

/-- Semantic index membership, with no occurrence of the proposed dimension formula. -/
theorem mem_indices_iff {n : ℕ} {a b s i : ℤ}
    (hb : InBounds n a b s) (hs : s ≠ 0) :
    i ∈ indices n a b s ↔ ∃ k : ℕ, continues a b s k ∧ i = a + (k : ℤ) * s := by
  simp only [indices, ordinals, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨_, hk⟩, hi⟩
    exact ⟨k, hk, hi.symm⟩
  · rintro ⟨k, hk, hi⟩
    exact ⟨k, ⟨(continues_bounds hb hs hk).1, hk⟩, hi.symm⟩

/-- Count correctness for arbitrary normalized signed endpoints and nonzero signed stride. -/
theorem card_indices {n : ℕ} {a b s : ℤ}
    (hb : InBounds n a b s) (hs : s ≠ 0) :
    (indices n a b s).card = length a b s := by
  rw [indices, Finset.card_image_of_injective _ (affine_injective hs),
    ordinals_eq_range hb hs, Finset.card_range]

/-- A raw Python slice. `none` represents an omitted bound or step, not an integer. -/
structure RawSlice where
  start : Option ℤ := none
  stop : Option ℤ := none
  step : Option ℤ := none

/-- Only an omitted step defaults to one; an explicit zero remains invalid. -/
def RawSlice.stride (r : RawSlice) : ℤ := r.step.getD 1

/-- Negative explicit bounds are relative to the parent dimension, then clipped. -/
def normalizeBound (n lo hi fallback : ℤ) : Option ℤ → ℤ
  | none => fallback
  | some x => max lo (min hi (if x < 0 then x + n else x))

/-- Normalized start, including direction-dependent defaults and clipping. -/
def RawSlice.first (r : RawSlice) (n : ℕ) : ℤ :=
  if 0 < r.stride then normalizeBound n 0 n 0 r.start
  else normalizeBound n (-1) (n - 1) (n - 1) r.start

/-- Normalized exclusive stop. For negative steps, an omitted stop stays `-1`. -/
def RawSlice.last (r : RawSlice) (n : ℕ) : ℤ :=
  if 0 < r.stride then normalizeBound n 0 n n r.stop
  else normalizeBound n (-1) (n - 1) (-1) r.stop

private theorem normalizeBound_bounds {n lo hi fallback : ℤ}
    (hf : lo ≤ fallback ∧ fallback ≤ hi) (raw : Option ℤ) :
    lo ≤ normalizeBound n lo hi fallback raw ∧
      normalizeBound n lo hi fallback raw ≤ hi := by
  cases raw with
  | none => exact hf
  | some x => simp only [normalizeBound]; omega

/-- All raw signed bounds normalize into the correct endpoint interval, including `n = 0`. -/
theorem RawSlice.inBounds (r : RawSlice) (n : ℕ) :
    InBounds n (r.first n) (r.last n) r.stride := by
  by_cases hp : 0 < r.stride
  · simp only [InBounds, RawSlice.first, RawSlice.last, hp, ite_true]
    have ha := normalizeBound_bounds
      (n := (n : ℤ)) (lo := 0) (hi := n) (fallback := 0) (by omega) r.start
    have hb := normalizeBound_bounds
      (n := (n : ℤ)) (lo := 0) (hi := n) (fallback := n) (by omega) r.stop
    exact ⟨ha.1, ha.2, hb.1, hb.2⟩
  · simp only [InBounds, RawSlice.first, RawSlice.last, hp, ite_false]
    have ha := normalizeBound_bounds
      (n := (n : ℤ)) (lo := -1) (hi := n - 1) (fallback := n - 1) (by omega) r.start
    have hb := normalizeBound_bounds
      (n := (n : ℤ)) (lo := -1) (hi := n - 1) (fallback := -1) (by omega) r.stop
    omega

/-- The selected parent indices of a raw slice, before using any dimension formula. -/
def RawSlice.indices (r : RawSlice) (n : ℕ) : Finset ℤ :=
  PythonSlice.indices n (r.first n) (r.last n) r.stride

/-- The general symbolic dimension expression. -/
def RawSlice.dimension (r : RawSlice) (n : ℕ) : ℤ :=
  max 0 ⌈((r.last n : ℚ) - r.first n) / r.stride⌉

/-- Universal count correctness: every raw integer bound, every nonzero signed stride. -/
theorem RawSlice.card_indices (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    ((r.indices n).card : ℤ) = r.dimension n := by
  rw [RawSlice.indices, PythonSlice.card_indices (r.inBounds n) hs, length_eq_max_ceiling]
  rfl

/-- Regardless of signs or clipping, a valid slice dimension lies between zero and its parent size. -/
theorem RawSlice.dimension_bounds (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    0 ≤ r.dimension n ∧ r.dimension n ≤ n := by
  have hlen : length (r.first n) (r.last n) r.stride ≤ n := by
    by_contra h
    have hk := (lt_length_iff hs).1 (show n < length (r.first n) (r.last n) r.stride by omega)
    have := (continues_bounds (r.inBounds n) hs hk).1
    omega
  change 0 ≤ max 0 _ ∧ max 0 _ ≤ _
  rw [← length_eq_max_ceiling]
  exact ⟨by positivity, by exact_mod_cast hlen⟩

/-- The parent index at ordinal `k`, with the bounds proved for both stride directions. -/
def RawSlice.index (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0)
    (k : Fin (length (r.first n) (r.last n) r.stride)) : Fin n :=
  ⟨(r.first n + (k.val : ℤ) * r.stride).toNat, by
    have h := continues_bounds (r.inBounds n) hs ((lt_length_iff hs).1 k.isLt)
    omega⟩

/-- The signed affine entry formula is preserved by conversion to a finite source index. -/
@[simp] theorem RawSlice.index_val (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0)
    (k : Fin (length (r.first n) (r.last n) r.stride)) :
    ((r.index n hs k).val : ℤ) = r.first n + (k.val : ℤ) * r.stride := by
  have h := continues_bounds (r.inBounds n) hs ((lt_length_iff hs).1 k.isLt)
  simp only [RawSlice.index]
  omega

theorem RawSlice.index_injective (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    Function.Injective (r.index n hs) := by
  intro i j h
  have hv := congrArg (fun k : Fin n => (k.val : ℤ)) h
  simp only [RawSlice.index_val] at hv
  exact Fin.ext (affine_injective hs hv)

/-- Every selected parent index occurs in the sample's index type. -/
theorem RawSlice.mem_indices_iff (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) (i : Fin n) :
    (i.val : ℤ) ∈ r.indices n ↔ ∃ k, r.index n hs k = i := by
  rw [RawSlice.indices, PythonSlice.mem_indices_iff (r.inBounds n) hs]
  constructor
  · rintro ⟨k, hk, hi⟩
    refine ⟨⟨k, (lt_length_iff hs).2 hk⟩, ?_⟩
    apply Fin.ext
    have hv := r.index_val n hs ⟨k, (lt_length_iff hs).2 hk⟩
    dsimp only at hv
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, (lt_length_iff hs).1 k.isLt, r.index_val n hs k⟩

/-- A sign-only indicator for strict negativity; it is zero at `x = 0`. -/
theorem sign_indicator_eq_if (x : ℤ) :
    (x.sign ^ 2 - x.sign) / 2 = if x < 0 then 1 else 0 := by
  by_cases hn : x < 0
  · simp [Int.sign_eq_neg_one_of_neg hn, hn]
  · by_cases hz : x = 0
    · subst x
      decide
    · have hp : 0 < x := by omega
      simp [Int.sign_eq_one_of_pos hp, hn]

/-- Clipping limits and negative-bound adjustment, with no sign-dependent branches. -/
def normalizeBySign (n s x : ℤ) : ℤ :=
  max (-((s.sign ^ 2 - s.sign) / 2))
    (min (n - (s.sign ^ 2 - s.sign) / 2) (x + n * ((x.sign ^ 2 - x.sign) / 2)))

/-- Sign-function start formula; omission remains distinct from any explicit integer. -/
def RawSlice.firstBySign (r : RawSlice) (n : ℕ) : ℤ :=
  match r.start with
  | none => ((r.stride.sign ^ 2 - r.stride.sign) / 2) * (n - 1)
  | some x => normalizeBySign n r.stride x

/-- Sign-function stop formula; an omitted reverse stop is the sentinel `-1`. -/
def RawSlice.lastBySign (r : RawSlice) (n : ℕ) : ℤ :=
  match r.stop with
  | none => (1 - (r.stride.sign ^ 2 - r.stride.sign) / 2) * n -
      (r.stride.sign ^ 2 - r.stride.sign) / 2
  | some x => normalizeBySign n r.stride x

/-- Agreement with the direction-dependent start normalization. -/
theorem RawSlice.first_eq_sign (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    r.first n = r.firstBySign n := by
  by_cases hp : 0 < r.stride
  · have hn : ¬r.stride < 0 := by omega
    cases hraw : r.start <;>
      simp [RawSlice.first, RawSlice.firstBySign, normalizeBySign, add_ite,
        sign_indicator_eq_if, hp, hn, normalizeBound, hraw]
  · have hn : r.stride < 0 := by omega
    cases hraw : r.start <;>
      simp [RawSlice.first, RawSlice.firstBySign, normalizeBySign, add_ite,
        sign_indicator_eq_if, hp, hn, normalizeBound, hraw]

/-- Agreement with the direction-dependent stop normalization. -/
theorem RawSlice.last_eq_sign (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    r.last n = r.lastBySign n := by
  by_cases hp : 0 < r.stride
  · have hn : ¬r.stride < 0 := by omega
    cases hraw : r.stop <;>
      simp [RawSlice.last, RawSlice.lastBySign, normalizeBySign, add_ite,
        sign_indicator_eq_if, hp, hn, normalizeBound, hraw]
  · have hn : r.stride < 0 := by omega
    cases hraw : r.stop <;>
      simp [RawSlice.last, RawSlice.lastBySign, normalizeBySign, add_ite,
        sign_indicator_eq_if, hp, hn, normalizeBound, hraw]

/-- The slice dimension expressed using sign, min, max and ceiling. -/
def RawSlice.dimensionBySign (r : RawSlice) (n : ℕ) : ℤ :=
  max 0 ⌈((r.lastBySign n : ℚ) - r.firstBySign n) / r.stride⌉

theorem RawSlice.dimension_eq_sign (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    r.dimension n = r.dimensionBySign n := by
  rw [RawSlice.dimension, r.first_eq_sign n hs, r.last_eq_sign n hs]
  rfl

/-- Correctness of the sign-based formula for arbitrary raw bounds and a nonzero signed step. -/
theorem RawSlice.card_indices_eq_sign (r : RawSlice) (n : ℕ) (hs : r.stride ≠ 0) :
    ((r.indices n).card : ℤ) = r.dimensionBySign n := by
  rw [r.card_indices n hs, r.dimension_eq_sign n hs]

/-- Explicit symbolic bounds: no omission handling or sign-dependent conditionals appear
in the right-hand side. The parent dimension is arbitrary and the stride may have either sign. -/
theorem card_explicit_indices_eq_sign (n : ℕ) (a b s : ℤ) (hs : s ≠ 0) :
    ((({ start := some a, stop := some b, step := some s } : RawSlice).indices n).card : ℤ) =
      max 0 ⌈((normalizeBySign n s b : ℚ) - normalizeBySign n s a) / s⌉ := by
  simpa [RawSlice.dimensionBySign, RawSlice.firstBySign, RawSlice.lastBySign, RawSlice.stride]
    using ({ start := some a, stop := some b, step := some s } : RawSlice).card_indices_eq_sign
      n hs

end SympyProofs.PythonSlice
