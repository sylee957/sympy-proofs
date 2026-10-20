module

public import SympyProofs.Python.ByteArray
public import SympyProofs.Python.Bytes.Int

/-!
# Python-integer interface to bytearray

Python-visible lengths, counts, indices, byte values and `find` results use `I`.
`size` and the natural-number slice length are backend observations for proofs.
As with the underlying class, indexed operations require nonnegative in-bounds
indices, assigned byte values must lie in `[0, 256)`, and searches require a
nonnegative start. The supported search pattern is one byte. This is a value
model, not exception handling or a model of mutable object aliases.
-/

@[expose] public section

namespace PythonByteArray.IntAPI

variable {I B : Type} [PythonInt I] [PythonByteArray B]

def len (I : Type) [PythonInt I] (bytes : B) : I := (size bytes : I)

def «repeat» (bytes : B) (count : I) : B := repeatBytes bytes (PythonInt.toNat count)

def get (bytes : B) (index : I) : I :=
  ((getByte bytes (PythonInt.toNat index)).toNat : I)

def set (bytes : B) (index value : I) : B :=
  set! bytes (PythonInt.toNat index) (UInt8.ofNat (PythonInt.toNat value))

/-- Positive-stride, equal-length slice assignment; proof arguments have no runtime cost. -/
def setSlice (bytes : B) (start step : I) (replacement : Bytes B)
    (hstep : 0 < PythonInt.toInt step)
    (hlen : PythonBytes.size replacement =
      sliceLength bytes (PythonInt.toNat start) (PythonInt.toNat step)) : B :=
  PythonByteArray.setSlice bytes (PythonInt.toNat start) (PythonInt.toNat step) replacement
    (by unfold PythonInt.toNat; omega) hlen

/-- Single-byte `bytes.find(pattern, start)`. The `-1` result stays signed. -/
def find (bytes : B) (pattern : Bytes B) (start : I)
    (_hpattern : PythonBytes.size pattern = 1) : I :=
  (PythonByteArray.find bytes (PythonBytes.getByte pattern 0) (PythonInt.toNat start) : I)

@[simp] theorem toInt_len (bytes : B) :
    PythonInt.toInt (len I bytes) = (size bytes : ℤ) := by simp [len]

@[simp] theorem size_repeat (bytes : B) (count : I) :
    size («repeat» bytes count) = size bytes * PythonInt.toNat count :=
  PythonByteArray.size_repeat _ _

@[simp] theorem toInt_get (bytes : B) (index : I) :
    PythonInt.toInt (get bytes index) =
      ((getByte bytes (PythonInt.toNat index)).toNat : ℤ) := by simp [get]

@[simp] theorem size_set (bytes : B) (index value : I) :
    size (set bytes index value) = size bytes := by simp [set]

/-- Within Python's valid domain, byte conversion loses no information. -/
theorem get_set_same (bytes : B) (index value : I)
    (hi : PythonInt.toNat index < size bytes)
    (hv : 0 ≤ PythonInt.toInt value ∧ PythonInt.toInt value < 256) :
    get (set bytes index value) index = value := by
  apply PythonInt.toInt_injective
  rw [toInt_get, set, PythonByteArray.get_set! _ _ _ hi, ite_eq_left rfl]
  rw [UInt8.toNat_ofNat_of_lt' (by unfold PythonInt.toNat; change _ < 256; omega)]
  exact (PythonInt.toInt_eq_natCast value hv.1).symm

@[simp] theorem size_setSlice (bytes : B) (start step : I) (replacement : Bytes B)
    (hstep : 0 < PythonInt.toInt step) (hlen) :
    size (setSlice bytes start step replacement hstep hlen) = size bytes :=
  PythonByteArray.size_setSlice _ _ _ _ _ _

@[simp] theorem toInt_find (bytes : B) (pattern : Bytes B) (start : I) (hpattern) :
    PythonInt.toInt (find bytes pattern start hpattern) =
      PythonByteArray.find bytes (PythonBytes.getByte pattern 0) (PythonInt.toNat start) := by
  simp [find]

/-- Number of inspected buffer bytes in a sequential first-match search. -/
def findVisits (bytes : B) (pattern : Bytes B) (start : I) : ℕ :=
  let result := PythonByteArray.find bytes (PythonBytes.getByte pattern 0) (PythonInt.toNat start)
  if result = -1 then size bytes - PythonInt.toNat start
  else result.toNat + 1 - PythonInt.toNat start

/-- A search inspects at most the remaining suffix, including when it has no match. -/
theorem findVisits_le (bytes : B) (pattern : Bytes B) (start : I) :
    findVisits bytes pattern start ≤ size bytes - PythonInt.toNat start := by
  obtain h | h := find_spec bytes (PythonBytes.getByte pattern 0) (PythonInt.toNat start)
  · simp [findVisits, h.1]
  · unfold findVisits
    rw [ite_eq_right (by omega)]
    omega

end PythonByteArray.IntAPI
