module

public import SympyProofs.Python.Bytes
public import Std.Tactic.Do
public import Std.WP

/-!
# Abstract Python bytearray interface

`PythonByteArray B` specifies operations and their value semantics on an abstract
carrier `B`. It does not prescribe storage or an implementation. Instances must
prove every law. The syntax `bytearray (b[0x01]) * count`, indexing, and the methods
below use only this interface. A native realization is provided separately in
`SympyProofs.Python.ByteArray.Native`.

The supported domain has byte-valued elements, nonnegative indices, positive
slice strides, and equal-length slice assignment. Negative repetition counts
produce empty arrays. Indexed reads and writes correspond to Python on in-bounds
indices. Python exceptions, negative indexing, and mutable aliasing are outside
this value model.
-/

@[expose] public section

/-- Python bytearray operations and their laws, independent of the carrier's representation. -/
class PythonByteArray (B : Type) where
  /-- The separate immutable bytes carrier accepted by this bytearray implementation. -/
  Bytes : Type
  /-- Operations and laws for the associated immutable bytes type. -/
  bytesModel : PythonBytes Bytes
  /-- Convert immutable bytes into a bytearray, as in `bytearray(b'\x01')`. -/
  ofBytes : Bytes → B
  /-- Number of bytes: Python's `len`, represented internally as a natural number. -/
  size : B → ℕ
  /-- Read a byte at a nonnegative index; Python correspondence requires an in-bounds index. -/
  getByte : B → ℕ → UInt8
  /-- Repeat the whole sequence a nonnegative number of times, as in `bytes * count`. -/
  repeatBytes : B → ℕ → B
  /-- Return the result of `bytes[i] = value`; Python correspondence requires `i < size bytes`. -/
  set! : B → ℕ → UInt8 → B
  /-- Assign `replacement` to `bytes[start::step]`, requiring a positive step and matching length. -/
  setSlice : (bytes : B) → (start step : ℕ) → (replacement : Bytes) →
    (hstep : 0 < step) →
    (hlen : bytesModel.size replacement = (size bytes - start + step - 1) / step) → B
  /-- Find the first occurrence of a byte from `start`, returning its index or Python's `-1`. -/
  find : B → UInt8 → ℕ → ℤ
  /-- Construction preserves the input sequence's length. -/
  size_ofBytes : ∀ values, size (ofBytes values) = bytesModel.size values
  /-- Conversion preserves every in-bounds byte of the immutable input. -/
  get_ofBytes : ∀ values i, i < bytesModel.size values →
    getByte (ofBytes values) i = bytesModel.getByte values i
  /-- Repetition multiplies the original length by the repetition count. -/
  size_repeat : ∀ bytes count, size (repeatBytes bytes count) = size bytes * count
  /-- Each valid position in a repetition reads the corresponding position in the original block. -/
  get_repeat : ∀ bytes count i, i < size (repeatBytes bytes count) →
    getByte (repeatBytes bytes count) i = getByte bytes (i % size bytes)
  /-- Indexed assignment preserves the length. -/
  size_set! : ∀ bytes i value, size (set! bytes i value) = size bytes
  /-- An in-bounds assignment changes exactly the selected byte. -/
  get_set! : ∀ bytes i value, i < size bytes → ∀ j,
    getByte (set! bytes i value) j = if i = j then value else getByte bytes j
  /-- Equal-length slice assignment preserves the bytearray's total length. -/
  size_setSlice : ∀ bytes start step replacement hstep hlen,
    size (setSlice bytes start step replacement hstep hlen) = size bytes
  /-- Slice positions receive replacement bytes in order; all other positions are unchanged. -/
  get_setSlice : ∀ bytes start step replacement hstep hlen j,
    getByte (setSlice bytes start step replacement hstep hlen) j =
      if j ∈ ForIn.toList (⟨start, size bytes, step, hstep⟩ : Std.Legacy.Range)
      then bytesModel.getByte replacement ((j - start) / step) else getByte bytes j
  /-- Search returns `-1` exactly when the suffix has no match, otherwise its earliest match. -/
  find_spec : ∀ bytes value start,
    let i := find bytes value start
    (i = -1 ∧ ∀ j, start ≤ j → j < size bytes → getByte bytes j ≠ value) ∨
      (0 ≤ i ∧ start ≤ i.toNat ∧ i.toNat < size bytes ∧ getByte bytes i.toNat = value ∧
        ∀ j, start ≤ j → j < i.toNat → getByte bytes j ≠ value)

attribute [instance_reducible] PythonByteArray.bytesModel
attribute [instance] PythonByteArray.bytesModel

/-- The Python bytearray constructor applied to immutable bytes. -/
def bytearray {B : Type} [PythonByteArray B] (values : PythonByteArray.Bytes B) : B :=
  PythonByteArray.ofBytes values

namespace PythonByteArray

open scoped PythonBytes

variable {B : Type} [PythonByteArray B]

instance : GetElem B Nat UInt8 (fun bytes i => i < size bytes) where
  getElem bytes i _ := getByte bytes i

instance : HMul B Nat B := ⟨repeatBytes⟩

/-- Signed repetition counts have Python's empty-result behavior for negative values. -/
instance : HMul B Int B := ⟨fun bytes count => repeatBytes bytes count.toNat⟩

/-- Integer-valued length for Python expressions involving signed subtraction. -/
def len (bytes : B) : ℤ := size bytes

/-- Observe the byte values without accessing the implementation's storage. -/
def toArray (bytes : B) : Array UInt8 :=
  Array.ofFn (fun i : Fin (size bytes) => getByte bytes i.val)

attribute [simp] size_set! size_setSlice

@[simp] theorem size_bytearray (values : Bytes B) :
    size (bytearray values : B) = PythonBytes.size values := size_ofBytes values

@[simp] theorem size_mul (bytes : B) (count : ℕ) :
    size (bytes * count) = size bytes * count := size_repeat bytes count

@[simp] theorem size_mul_int (bytes : B) (count : ℤ) :
    size (bytes * count) = size bytes * count.toNat := size_repeat bytes count.toNat

theorem getElem!_eq_getByte (bytes : B) (i : ℕ) (hi : i < size bytes) :
    bytes[i]! = getByte bytes i := by
  rw [getElem!_pos bytes i hi]
  rfl

/-- Number of positions in the positive-stride slice `bytes[start::step]`. -/
def sliceLength (bytes : B) (start step : ℕ) : ℕ :=
  (size bytes - start + step - 1) / step

theorem sliceLength_eq (bytes : B) (start step : ℕ)
    (hstart : start < size bytes) (hstep : 0 < step) :
    sliceLength bytes start step = (size bytes - 1 - start) / step + 1 := by
  unfold sliceLength
  rw [show size bytes - start + step - 1 = (size bytes - 1 - start) + step by omega,
    Nat.add_div_right _ hstep]

/-- The signed Python count also handles empty and past-end slices. -/
theorem sliceLength_eq_python_count (bytes : B) (start step : ℕ)
    (hstep : 0 < step) :
    sliceLength bytes start step = ((len bytes - 1 - start).fdiv step + 1).toNat := by
  by_cases hstart : start < size bytes
  · rw [sliceLength_eq bytes start step hstart hstep]
    have hsub : len bytes - 1 - start = ((size bytes - 1 - start : ℕ) : ℤ) := by
      unfold len
      omega
    rw [hsub, ← Int.ofNat_fdiv]
    norm_cast
  · have hneg : len bytes - 1 - start < 0 := by unfold len; omega
    have hdiv := Int.ediv_neg_of_neg_of_pos hneg (show (0 : ℤ) < step by omega)
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]
    have hzero : sliceLength bytes start step = 0 := by
      simp only [sliceLength, Nat.sub_eq_zero_of_le (by omega : size bytes ≤ start),
        Nat.zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega

theorem size_singleton_mul_sliceCount (bytes : B) (value : UInt8)
    (start step : ℕ) (hstep : 0 < step) :
    PythonBytes.size ((b[value] : Bytes B) * ((len bytes - 1 - start).fdiv step + 1)) =
      sliceLength bytes start step := by
  simpa using (sliceLength_eq_python_count bytes start step hstep).symm

/-- Every selected position reads an in-bounds replacement byte. -/
theorem slice_index_lt (bytes : B) (start step j : ℕ) (hstep : 0 < step)
    (hj : j ∈ ForIn.toList (⟨start, size bytes, step, hstep⟩ : Std.Legacy.Range)) :
    (j - start) / step < sliceLength bytes start step := by
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (by simpa using hj)
  simpa [sliceLength, Nat.mul_div_cancel_left _ hstep] using hi

/-- A type synonym retaining method notation for an otherwise abstract carrier. -/
abbrev Value (B : Type) := B

namespace Value

/-- These method aliases introduce no storage and use only the abstract operations. -/
abbrev size (bytes : Value B) : ℕ := PythonByteArray.size bytes
abbrev len (bytes : Value B) : ℤ := PythonByteArray.len bytes
abbrev set! (bytes : Value B) (i : ℕ) (value : UInt8) : Value B :=
  PythonByteArray.set! bytes i value
abbrev setSlice (bytes : Value B) (start step : ℕ) (replacement : Bytes B)
    (hstep : 0 < step) (hlen : PythonBytes.size replacement = PythonByteArray.sliceLength bytes start step) :
    Value B := PythonByteArray.setSlice bytes start step replacement hstep hlen
abbrev find (bytes : Value B) (value : UInt8) (start : ℕ) : ℤ :=
  PythonByteArray.find bytes value start

end Value

end PythonByteArray
