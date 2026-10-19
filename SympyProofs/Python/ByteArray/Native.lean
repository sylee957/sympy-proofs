module

public import SympyProofs.Python.ByteArray
public import SympyProofs.Python.Bytes.Native
public import Init.Data.ByteArray.Lemmas

/-!
# Native realization of the Python bytearray interface

This module implements the abstract operations using Lean's `ByteArray` and
proves the interface laws. Algorithm modules only import the interface;
executables choose this realization by supplying `PythonByteArray.Native`.
-/

@[expose] public section

namespace Python.ByteArray

open scoped Std.WP

/-- Find the first occurrence of a byte at or after `start`. -/
def findByte (bytes : ByteArray) (value : UInt8) (start : ℕ) : Option ℕ := Id.run do
  for i in [start:bytes.size] do
    if bytes[i]! = value then
      return some i
  return none

/-- The result contract of Python's byte search, using `none` for `-1`. -/
def FindSpec (bytes : ByteArray) (value : UInt8) (start : ℕ) (result : Option ℕ) : Prop :=
  match result with
  | none => ∀ i, start ≤ i → i < bytes.size → bytes[i]! ≠ value
  | some i => start ≤ i ∧ i < bytes.size ∧ bytes[i]! = value ∧
      ∀ j, start ≤ j → j < i → bytes[j]! ≠ value

/-- `find` returns the first matching byte, or certifies that the suffix has none. -/
theorem findByte_spec (bytes : ByteArray) (value : UInt8) (start : ℕ) :
    FindSpec bytes value start (findByte bytes value start) := by
  generalize he : findByte bytes value start = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref suff (ret, _) =>
      match ret with
      | none => ∀ i ∈ pref, bytes[i]! ≠ value
      | some result => suff = [] ∧ FindSpec bytes value start result
  all_goals try simp_all +zetaDelta [FindSpec]
  case vc3 =>
    rename_i ret state hinv hret
    intro i hstart hi
    simpa [getElem!_pos bytes i hi] using hinv i hstart (by omega)
  case vc4 =>
    rename_i pref i suff ret state hs hinv hi
    cases ret with
    | some r => simp at hinv
    | none =>
      simp only at hinv
      obtain ⟨j, hj, hpref, htail⟩ := List.range'_eq_append_iff.mp hs
      have hhead := List.range'_eq_cons_iff.mp htail.symm
      refine ⟨by omega, by omega, ?_⟩
      intro t ht hti
      apply hinv t
      rw [hpref]
      simp only [List.mem_range']
      exact ⟨t - start, by omega, by omega⟩
  case vc5 =>
    rename_i pref i suff ret state hs hinv hi
    cases ret with
    | some r => simp at hinv
    | none =>
      simp only at hinv
      intro j hj
      rcases hj with hj | rfl
      · exact hinv j hj
      · exact hi

end Python.ByteArray

/-- Concrete carrier backed by Lean's native byte array. -/
structure PythonByteArray.Native where
  storage : ByteArray

/-- Convert immutable bytes to a separate bytearray value. -/
def PythonByteArray.Native.ofBytes (values : PythonBytes.Native) : PythonByteArray.Native :=
  ⟨⟨values.contents⟩⟩

namespace PythonByteArray.Native

open scoped Std.WP

def size (bytes : PythonByteArray.Native) : ℕ := bytes.storage.size

local instance : GetElem PythonByteArray.Native Nat UInt8 (fun bytes i => i < bytes.size) where
  getElem bytes i hi := bytes.storage[i]

/-- Repetition of the whole byte sequence, including multi-byte sequences. -/
def repeatBytes (bytes : PythonByteArray.Native) (count : ℕ) : PythonByteArray.Native :=
  ⟨⟨Array.ofFn (fun i : Fin (bytes.size * count) => bytes.storage[i.val % bytes.size]!)⟩⟩

local instance : HMul PythonByteArray.Native Nat PythonByteArray.Native := ⟨repeatBytes⟩

/-- Python repetition by a negative integer produces an empty bytearray. -/
local instance : HMul PythonByteArray.Native Int PythonByteArray.Native := ⟨fun bytes count => repeatBytes bytes count.toNat⟩

@[simp] theorem size_ofBytes (values : PythonBytes.Native) :
    (ofBytes values).size = values.size := rfl

@[simp] theorem size_mul (bytes : PythonByteArray.Native) (count : ℕ) :
    (bytes * count).size = bytes.size * count := by
  change (Array.ofFn (fun i : Fin (bytes.size * count) =>
    bytes.storage[i.val % bytes.size]!)).size = bytes.size * count
  exact Array.size_ofFn

@[simp] theorem size_mul_int (bytes : PythonByteArray.Native) (count : ℤ) :
    (bytes * count).size = bytes.size * count.toNat := by
  exact size_mul bytes count.toNat

/-- Each repeated block has exactly the bytes of the original sequence. -/
theorem get_mul (bytes : PythonByteArray.Native) (count i : ℕ) (hi : i < (bytes * count).size) :
    (bytes * count)[i] = bytes.storage[i % bytes.size]! := by
  exact Array.getElem_ofFn ..

/-- Indexed assignment; the caller must use an in-bounds index for Python correspondence. -/
def set! (bytes : PythonByteArray.Native) (i : ℕ) (value : UInt8) : PythonByteArray.Native :=
  ⟨bytes.storage.set! i value⟩

@[simp] theorem size_set! (bytes : PythonByteArray.Native) (i : ℕ) (value : UInt8) :
    (bytes.set! i value).size = bytes.size := by simp [set!, size]

/-- Equal-length extended-slice assignment. The replacement length is checked by a proof. -/
def setSlice (bytes : PythonByteArray.Native) (start step : ℕ) (replacement : PythonBytes.Native)
    (hstep : 0 < step) (_hlen : replacement.size = (bytes.size - start + step - 1) / step) :
    PythonByteArray.Native := Id.run do
  let mut result := bytes.storage
  for i in (⟨start, bytes.size, step, hstep⟩ : Std.Legacy.Range) do
    result := result.set! i replacement.contents[(i - start) / step]!
  return ⟨result⟩

/-- Assignment changes exactly the slice positions to the corresponding replacement bytes. -/
theorem setSlice_spec (bytes : PythonByteArray.Native) (start step : ℕ)
    (replacement : PythonBytes.Native) (hstep : 0 < step)
    (hlen : replacement.size = (bytes.size - start + step - 1) / step) :
    let range : Std.Legacy.Range := ⟨start, bytes.size, step, hstep⟩
    (bytes.setSlice start step replacement hstep hlen).size = bytes.size ∧
      ∀ j, (bytes.setSlice start step replacement hstep hlen).storage[j]! =
        if j ∈ ForIn.toList range then replacement.contents[(j - start) / step]!
        else bytes.storage[j]! := by
  dsimp only
  generalize he : bytes.setSlice start step replacement hstep hlen = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ current => current.size = bytes.size ∧
      ∀ j, current[j]! = if j ∈ pref then replacement.contents[(j - start) / step]!
        else bytes.storage[j]!
  case vc1 => simp +zetaDelta [size]
  case vc2 => simp_all +zetaDelta [size]
  case vc3 =>
    rename_i pref i suff hs current hinv
    dsimp +zetaDelta only
    have hmem : i ∈ ForIn.toList (⟨start, bytes.size, step, hstep⟩ : Std.Legacy.Range) := by
      rw [hs]; simp
    have hib : i < bytes.size :=
      (Std.Legacy.Range.mem_of_mem_range'
        (r := ⟨start, bytes.size, step, hstep⟩) (by simpa using hmem)).upper
    refine ⟨by simpa using hinv.1, ?_⟩
    intro j
    rw [ByteArray.getElem!_set! _ _ _ _ (by omega), hinv.2]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij]

@[simp] theorem size_setSlice (bytes : PythonByteArray.Native) (start step : ℕ)
    (replacement : PythonBytes.Native) (hstep : 0 < step)
    (hlen : replacement.size = (bytes.size - start + step - 1) / step) :
    (bytes.setSlice start step replacement hstep hlen).size = bytes.size :=
  (setSlice_spec bytes start step replacement hstep hlen).1

/-- Python's single-byte `find`, including the signed `-1` sentinel. -/
def find (bytes : PythonByteArray.Native) (value : UInt8) (start : ℕ) : ℤ :=
  match Python.ByteArray.findByte bytes.storage value start with
  | none => -1
  | some i => i

/-- Search returns either `-1` with no match, or the first matching index. -/
theorem find_spec (bytes : PythonByteArray.Native) (value : UInt8) (start : ℕ) :
    let i := bytes.find value start
    (i = -1 ∧ ∀ j, start ≤ j → j < bytes.size → bytes.storage[j]! ≠ value) ∨
      (0 ≤ i ∧ start ≤ i.toNat ∧ i.toNat < bytes.size ∧ bytes.storage[i.toNat]! = value ∧
        ∀ j, start ≤ j → j < i.toNat → bytes.storage[j]! ≠ value) := by
  have h := Python.ByteArray.findByte_spec bytes.storage value start
  unfold find
  cases he : Python.ByteArray.findByte bytes.storage value start with
  | none =>
    simp only [he, Python.ByteArray.FindSpec] at h
    exact Or.inl ⟨rfl, h⟩
  | some i =>
    simp only [he, Python.ByteArray.FindSpec] at h
    simp only [Int.toNat_natCast]
    exact Or.inr ⟨Int.natCast_nonneg i, h⟩

/-- The native implementation satisfies every law of the abstract interface. -/
instance : PythonByteArray PythonByteArray.Native where
  Bytes := PythonBytes.Native
  bytesModel := inferInstance
  ofBytes := ofBytes
  size := size
  getByte := fun bytes i => bytes.storage[i]!
  repeatBytes := repeatBytes
  set! := set!
  setSlice := setSlice
  find := find
  size_ofBytes := size_ofBytes
  get_ofBytes := by
    intro values i hi
    change (ofBytes values).storage[i]! = values.contents[i]!
    have hi' : i < values.contents.size := hi
    have hi'' : i < (ofBytes values).storage.size := hi'
    rw [getElem!_pos (ofBytes values).storage i hi'', getElem!_pos values.contents i hi']
    rfl
  size_repeat := size_mul
  get_repeat := by
    intro bytes count i hi
    rw [getElem!_pos (repeatBytes bytes count).storage i hi]
    exact get_mul bytes count i hi
  size_set! := size_set!
  get_set! := by
    intro bytes i value hi j
    exact ByteArray.getElem!_set! bytes.storage i value j hi
  size_setSlice := size_setSlice
  get_setSlice := fun bytes start step replacement hstep hlen j =>
    (setSlice_spec bytes start step replacement hstep hlen).2 j
  find_spec := find_spec

end PythonByteArray.Native
