module

public import SympyProofs.Python.Bytes
public import SympyProofs.Python.Int

/-!
# Python-integer interface to immutable bytes

The carrier laws in `PythonBytes` use natural lengths and `UInt8` storage values.
This interface exposes Python integers for lengths, repeat counts, indices, and
read results. Conversion to storage indices happens only here. Reads correspond
to Python for nonnegative in-bounds indices; negative indexing and exceptions
remain outside this interface. Negative repetition counts correctly give emptiness.
-/

@[expose] public section

namespace PythonBytes.IntAPI

variable {I S : Type} [PythonInt I] [PythonBytes S]

def len (I : Type) [PythonInt I] (bytes : S) : I := (size bytes : I)

def «repeat» (bytes : S) (count : I) : S := repeatBytes bytes (PythonInt.toNat count)

def get (bytes : S) (index : I) : I :=
  ((getByte bytes (PythonInt.toNat index)).toNat : I)

@[simp] theorem toInt_len (bytes : S) :
    PythonInt.toInt (len I bytes) = (size bytes : ℤ) := by simp [len]

@[simp] theorem size_repeat (bytes : S) (count : I) :
    size («repeat» bytes count) = size bytes * PythonInt.toNat count :=
  PythonBytes.size_repeat _ _

theorem size_repeat_of_nonpos (bytes : S) (count : I) (h : PythonInt.toInt count ≤ 0) :
    size («repeat» bytes count) = 0 := by
  simp [size_repeat, PythonInt.toNat, Int.toNat_of_nonpos h]

@[simp] theorem toInt_get (bytes : S) (index : I) :
    PythonInt.toInt (get bytes index) =
      ((getByte bytes (PythonInt.toNat index)).toNat : ℤ) := by simp [get]

end PythonBytes.IntAPI
