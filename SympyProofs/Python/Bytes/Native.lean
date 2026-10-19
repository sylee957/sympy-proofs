module

public import SympyProofs.Python.Bytes

/-!
# Native realization of immutable Python bytes

The carrier is distinct from the mutable-bytearray model. Its operations return
new values and expose no byte or slice assignment through the bytes interface.
-/

@[expose] public section

/-- Native immutable byte-sequence values. -/
structure PythonBytes.Native where
  contents : Array UInt8

namespace PythonBytes.Native

/-- Interpret literal byte values. -/
def literal (values : Array UInt8) : Native := ⟨values⟩

def size (bytes : Native) : ℕ := bytes.contents.size

/-- Repeat every byte in each block of the result. -/
def repeatBytes (bytes : Native) (count : ℕ) : Native :=
  ⟨Array.ofFn (fun i : Fin (size bytes * count) => bytes.contents[i.val % size bytes]!)⟩

/-- The native operations satisfy the immutable bytes contract. -/
instance : PythonBytes Native where
  literal := literal
  size := size
  getByte := fun bytes i => bytes.contents[i]!
  repeatBytes := repeatBytes
  size_literal := fun _ => rfl
  get_literal := by
    intro values i hi
    exact getElem!_pos values i hi
  size_repeat := by
    intro bytes count
    exact Array.size_ofFn
  get_repeat := by
    intro bytes count i hi
    rw [getElem!_pos (repeatBytes bytes count).contents i hi]
    exact Array.getElem_ofFn ..

end PythonBytes.Native
