module

public import SympyProofs.PythonSlice.Canonical

/-!
# Slicing a slice

Normalize the outer slice against the source length `n`, and the inner slice
against the outer length `m`. If their range parameters are `(A, B, s)` and
`(C, D, t)`, the composed progression has parameters
`(A + C*s, A + D*s, s*t)`.

The transformed endpoints can lie outside the source even when both slices are
valid. Encode them as explicit raw arguments; canonicalization preserves these
arguments, and sampling clips them for the product stride. The resulting slice
preserves the ordered sample.
-/

@[expose] public section

namespace SympyProofs.PythonSlice

private theorem continues_affine (a s c d t : ℤ) (hs : s ≠ 0) (ht : t ≠ 0)
    (k : ℕ) :
    continues (a + c*s) (a + d*s) (s*t) k ↔ continues c d t k := by
  have heq : a + c*s + (k : ℤ)*(s*t) = a + (c + (k : ℤ)*t)*s := by ring
  simp only [continues, heq]
  generalize c + (k : ℤ)*t = x
  rcases lt_or_gt_of_ne hs with hp | hp <;>
    rcases lt_or_gt_of_ne ht with hq | hq
  · have hu : 0 < s*t := mul_pos_of_neg_of_neg hp hq
    simp only [hu, not_lt_of_gt hq, ite_true, ite_false]
    constructor <;> intro h <;> nlinarith
  · have hu : ¬0 < s*t := le_of_lt (mul_neg_of_neg_of_pos hp hq) |>.not_gt
    simp only [hu, hq, ite_true, ite_false]
    constructor <;> intro h <;> nlinarith
  · have hu : ¬0 < s*t := le_of_lt (mul_neg_of_pos_of_neg hp hq) |>.not_gt
    simp only [hu, not_lt_of_gt hq, ite_false]
    constructor <;> intro h <;> nlinarith
  · have hu : 0 < s*t := mul_pos hp hq
    simp only [hu, hq, ite_true]
    constructor <;> intro h <;> nlinarith

/-- An affine change of coordinates multiplies the stride, including sign reversal. -/
theorem intRange_affine (a s c d t : ℤ) (hs : s ≠ 0) (ht : t ≠ 0) :
    intRange (a + c*s) (a + d*s) (s*t) (mul_ne_zero hs ht) =
      (intRange c d t ht).map (fun i => a + i*s) := by
  have hlen : length (a + c*s) (a + d*s) (s*t) = length c d t := by
    apply eq_of_forall_lt_iff
    intro k
    rw [lt_length_iff (mul_ne_zero hs ht), lt_length_iff ht]
    exact continues_affine a s c d t hs ht k
  simp only [intRange_eq_map_range, hlen, List.map_map]
  congr 1
  funext k
  simp only [Function.comp_apply]
  ring

/-- Clipping range endpoints preserves a progression whose emitted indices are
already in bounds. Encoding prevents Python's negative-index adjustment from
changing those endpoints before clipping. -/
private theorem intRange_clip_encoded (n : ℕ) (a b s : ℤ) (hs : s ≠ 0)
    (hb : ∀ k < length a b s, 0 ≤ a + (k : ℤ)*s ∧ a + (k : ℤ)*s < n) :
    intRange (normalizeBySign n s (encodeBound n a))
      (normalizeBySign n s (encodeBound n b)) s hs = intRange a b s hs := by
  simp only [normalizeBySign, decode_encodeBound]
  by_cases hp : 0 < s
  · have hn : ¬s < 0 := by omega
    simp only [sign_indicator_eq_if, hn, ite_false]
    norm_num only
    simp only [sub_zero]
    by_cases hab : a < b
    · have hzero : 0 < length a b s := (lt_length_iff hs).2 (by simp [continues, hp, hab])
      have ha := hb 0 hzero
      simp only [Nat.cast_zero, zero_mul, add_zero] at ha
      have hclamp : max 0 (min (n : ℤ) a) = a := by omega
      rw [hclamp]
      have hlen : length a (max 0 (min (n : ℤ) b)) s = length a b s := by
        apply eq_of_forall_lt_iff
        intro k
        rw [lt_length_iff hs, lt_length_iff hs]
        simp only [continues, hp, ite_true]
        constructor
        · intro hk; omega
        · intro hk
          have hbound := hb k ((lt_length_iff hs).2 (by simpa [continues, hp] using hk))
          omega
      simp only [intRange_eq_map_range, hlen]
    · have hzero : length a b s = 0 := by
        have h := (lt_length_iff (a := a) (b := b) (k := 0) hs)
        simp [continues, hp, hab] at h
        omega
      have hzero' : length (max 0 (min (n : ℤ) a)) (max 0 (min (n : ℤ) b)) s = 0 := by
        have h := (lt_length_iff (a := max 0 (min (n : ℤ) a))
          (b := max 0 (min (n : ℤ) b)) (k := 0) hs)
        simp only [continues, hp, ite_true, Nat.cast_zero, zero_mul, add_zero] at h
        omega
      simp [intRange_eq_map_range, hzero, hzero']
  · have hn : s < 0 := by omega
    simp only [sign_indicator_eq_if, hn, ite_true]
    by_cases hab : b < a
    · have hzero : 0 < length a b s := (lt_length_iff hs).2 (by simp [continues, hp, hab])
      have ha := hb 0 hzero
      simp only [Nat.cast_zero, zero_mul, add_zero] at ha
      have hclamp : max (-1) (min ((n : ℤ) - 1) a) = a := by omega
      rw [hclamp]
      have hlen : length a (max (-1) (min ((n : ℤ) - 1) b)) s = length a b s := by
        apply eq_of_forall_lt_iff
        intro k
        rw [lt_length_iff hs, lt_length_iff hs]
        simp only [continues, hp, ite_false]
        constructor
        · intro hk; omega
        · intro hk
          have hbound := hb k ((lt_length_iff hs).2 (by simpa [continues, hp] using hk))
          omega
      simp only [intRange_eq_map_range, hlen]
    · have hzero : length a b s = 0 := by
        have h := (lt_length_iff (a := a) (b := b) (k := 0) hs)
        simp [continues, hp, hab] at h
        omega
      have hzero' : length (max (-1) (min ((n : ℤ) - 1) a))
          (max (-1) (min ((n : ℤ) - 1) b)) s = 0 := by
        have h := (lt_length_iff (a := max (-1) (min ((n : ℤ) - 1) a))
          (b := max (-1) (min ((n : ℤ) - 1) b)) (k := 0) hs)
        simp only [continues, hp, ite_false, Nat.cast_zero, zero_mul, add_zero] at h
        omega
      simp [intRange_eq_map_range, hzero, hzero']

/-- Compose an inner raw slice with an outer raw slice and return reusable
canonical arguments relative to the original source. -/
def RawSlice.compose (n : ℕ) (r q : RawSlice) : CanonicalSlice :=
  let m := (r.dimensionBySign n).toNat
  let start := r.firstBySign n + q.firstBySign m * r.stride
  let stop := r.firstBySign n + q.lastBySign m * r.stride
  let step := r.stride * q.stride
  ({ start := some (encodeBound n start), stop := some (encodeBound n stop),
      step := some step } : RawSlice).canonical n

@[simp] theorem RawSlice.compose_step (r q : RawSlice) (n : ℕ) :
    (RawSlice.compose n r q).step = r.stride * q.stride := by
  simp [RawSlice.compose, RawSlice.stride]

private theorem RawSlice.composed_index_bounds (r q : RawSlice) (n : ℕ)
    (hs : r.stride ≠ 0) (ht : q.stride ≠ 0) {j : ℤ}
    (hj : j ∈ intRange (q.first (r.dimensionBySign n).toNat)
      (q.last (r.dimensionBySign n).toNat) q.stride ht) :
    0 ≤ r.firstBySign n + j*r.stride ∧ r.firstBySign n + j*r.stride < n := by
  have hb := q.range_bounds (r.dimensionBySign n).toNat ht hj
  have hnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hb.1
  have hk : j.toNat < (r.dimensionBySign n).toNat := by omega
  simpa only [hnat] using r.formula_bounds n hs ⟨j.toNat, hk⟩

/-- The composed slice enumerates the affine image of the inner slice range. -/
theorem RawSlice.compose_range (r q : RawSlice) (n : ℕ)
    (hs : r.stride ≠ 0) (ht : q.stride ≠ 0) :
    intRange ((RawSlice.compose n r q).toRawSlice.first n)
      ((RawSlice.compose n r q).toRawSlice.last n)
      (RawSlice.compose n r q).toRawSlice.stride (by simpa using mul_ne_zero hs ht) =
      (intRange (q.first (r.dimensionBySign n).toNat)
        (q.last (r.dimensionBySign n).toNat) q.stride ht).map
        (fun j => r.firstBySign n + j*r.stride) := by
  let m := (r.dimensionBySign n).toNat
  let a := r.firstBySign n
  let c := q.first m
  let d := q.last m
  let f : RawSlice :=
    { start := some (encodeBound n (a + c*r.stride))
      stop := some (encodeBound n (a + d*r.stride))
      step := some (r.stride*q.stride) }
  have hf : f.stride ≠ 0 := mul_ne_zero hs ht
  have heq : RawSlice.compose n r q = f.canonical n := by
    simp only [RawSlice.compose, q.first_eq_sign m ht, q.last_eq_sign m ht, f, a, c, d, m]
  simp only [heq, f.canonical_range n hf, f.first_eq_sign n hf, f.last_eq_sign n hf]
  change intRange (normalizeBySign n (r.stride*q.stride) (encodeBound n (a + c*r.stride)))
    (normalizeBySign n (r.stride*q.stride) (encodeBound n (a + d*r.stride)))
    (r.stride*q.stride) (mul_ne_zero hs ht) = _
  have hb : ∀ k < length (a + c*r.stride) (a + d*r.stride) (r.stride*q.stride),
      0 ≤ a + c*r.stride + (k : ℤ)*(r.stride*q.stride) ∧
        a + c*r.stride + (k : ℤ)*(r.stride*q.stride) < n := by
    intro k hk
    have hm := (mem_intRange (mul_ne_zero hs ht)).2 ⟨k, hk, rfl⟩
    rw [intRange_affine a r.stride c d q.stride hs ht] at hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    rw [← he]
    exact r.composed_index_bounds q n hs ht hj
  rw [intRange_clip_encoded n _ _ _ (mul_ne_zero hs ht) hb,
    intRange_affine a r.stride c d q.stride hs ht]

/-- The complete element formula, with the two affine index maps combined. -/
theorem RawSlice.compose_range_eq_formula (r q : RawSlice) (n : ℕ)
    (hs : r.stride ≠ 0) (ht : q.stride ≠ 0) :
    let m := (r.dimensionBySign n).toNat
    let A := r.firstBySign n
    let C := q.firstBySign m
    let s := r.stride
    let t := q.stride
    let L := q.dimensionBySign m
    intRange ((RawSlice.compose n r q).toRawSlice.first n)
      ((RawSlice.compose n r q).toRawSlice.last n)
      (RawSlice.compose n r q).toRawSlice.stride (by simpa using mul_ne_zero hs ht) =
      (List.range L.toNat).map (fun k : ℕ => A + C*s + (k : ℤ)*(s*t)) := by
  dsimp only
  rw [r.compose_range q n hs ht, q.range_eq_formula _ ht, List.map_map]
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply]
  ring

/-- The composed length is the inner slice length, computed against the outer length. -/
theorem RawSlice.compose_dimension (r q : RawSlice) (n : ℕ)
    (hs : r.stride ≠ 0) (ht : q.stride ≠ 0) :
    (RawSlice.compose n r q).toRawSlice.dimensionBySign n =
      q.dimensionBySign (r.dimensionBySign n).toNat := by
  have h := congrArg (fun xs : List ℤ => (xs.length : ℤ)) (r.compose_range q n hs ht)
  simpa only [RawSlice.range_length_eq_formula, List.length_map] using h

/-- Sampling twice is exactly sampling once with the composed canonical slice. -/
theorem sampleArray_compose {α : Type*} (v : Array α) (r q : RawSlice)
    (hs : r.stride ≠ 0) (ht : q.stride ≠ 0) :
    sampleArray (sampleArray v r) q = sampleArray v (RawSlice.compose v.size r q).toRawSlice := by
  let w := sampleArray v r
  have hsize : w.size = (r.dimensionBySign v.size).toNat := by
    have h := (sampleArray_eq_formula v r hs).2
    change (w.size : ℤ) = _ at h
    omega
  have hc : (RawSlice.compose v.size r q).toRawSlice.stride ≠ 0 := by
    simpa using mul_ne_zero hs ht
  change sample (fun i : Fin w.size => w[i]) q.start q.stop q.step =
    sample (fun i : Fin v.size => v[i]) _ _ _
  rw [sample_eq_pmap _ q ht, sample_eq_pmap _ _ hc]
  simp only [r.compose_range q v.size hs ht, ← hsize, List.pmap_map]
  apply congrArg List.toArray
  apply List.pmap_congr_left
  intro j hj hleft hright
  have hnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hleft.1
  have hjw : j.toNat < w.size := by omega
  have hk : j.toNat < (r.dimensionBySign v.size).toNat := by omega
  have hget := sample_getElem (fun i : Fin v.size => v[i]) r hs ⟨j.toNat, hk⟩
  change w[j.toNat]? = some (v[r.formulaIndex v.size hs ⟨j.toNat, hk⟩]) at hget
  rw [Array.getElem?_eq_getElem hjw] at hget
  simp only [Option.some.injEq, RawSlice.formulaIndex, hnat] at hget
  exact hget

/-- The same operation for stored canonical triples. -/
def CanonicalSlice.compose (n : ℕ) (r q : CanonicalSlice) : CanonicalSlice :=
  RawSlice.compose n r.toRawSlice q.toRawSlice

/-- The formula for two explicit slice triples, in the order used by SymPy's
`compose_slices`. Normalization and length are expanded as local formulas. -/
theorem CanonicalSlice.compose_eq_formula (n : ℕ) (s1 s2 : CanonicalSlice) :
    let delta := fun x : ℤ => (x.sign ^ 2 - x.sign) / 2
    let decode_bound := fun bound n : ℤ => bound + n * delta bound
    let normalize_bound := fun n step bound : ℤ =>
      let p := delta step
      max (-p) (min (n - p) (decode_bound bound n))
    let slice_shape_1d := fun (n : ℤ) (sl : CanonicalSlice) =>
      let A := normalize_bound n sl.step sl.start
      let B := normalize_bound n sl.step sl.stop
      max 0 ⌈((B : ℚ) - A) / sl.step⌉
    let start1 := s1.start
    let step1 := s1.step
    let start2 := s2.start
    let stop2 := s2.stop
    let step2 := s2.step
    let L1 := slice_shape_1d n s1
    let A1 := normalize_bound n step1 start1
    let A2 := normalize_bound L1 step2 start2
    let B2 := normalize_bound L1 step2 stop2
    let A_comp := A1 + A2 * step1
    let B_comp := A1 + B2 * step1
    let step_comp := step1 * step2
    let A_comp := A_comp - (n : ℤ) * delta A_comp
    let B_comp := B_comp - (n : ℤ) * delta B_comp
    CanonicalSlice.compose n s1 s2 =
      { start := A_comp, stop := B_comp, step := step_comp } := by
  dsimp only
  unfold CanonicalSlice.compose RawSlice.compose
  rw [RawSlice.canonical_eq_formula]
  simp only [CanonicalSlice.toRawSlice, RawSlice.dimensionBySign, RawSlice.firstBySign,
    RawSlice.lastBySign, RawSlice.stride, Option.getD_some, normalizeBySign, encodeBound]
  rw [Int.toNat_of_nonneg (le_max_left 0 _)]

/-- Canonicalizing both arguments before composition leaves the composed triple unchanged. -/
theorem RawSlice.compose_canonical (r q : RawSlice) (n : ℕ) :
    CanonicalSlice.compose n (r.canonical n) (q.canonical (r.dimensionBySign n).toNat) =
      RawSlice.compose n r q := by
  simp only [CanonicalSlice.compose, RawSlice.compose, r.canonical_dimension n,
    r.canonical_first n, q.canonical_first, q.canonical_last,
    CanonicalSlice.toRawSlice_stride, RawSlice.canonical_step]

/-- A flattened slice is still fixed by rebuilding through canonicalization. -/
theorem RawSlice.compose_idempotent (r q : RawSlice) (n : ℕ) :
    (RawSlice.compose n r q).toRawSlice.canonical n = RawSlice.compose n r q := by
  exact CanonicalSlice.toRawSlice_canonical _ n

end SympyProofs.PythonSlice
