module

public import SympyProofs.Python.Cost.Bytes
public import SympyProofs.Python.ByteArray.Int

/-!
# Costed bytearray operations

Buffer read/write counts describe a sequential mutable byte-buffer implementation.
Lean's persistent implementation may copy on writes; that is not asserted to be
Python's allocation behavior. `created` records payload volume, not heap headers,
allocator reuse, garbage collection, or peak live memory. Preconditions are those
of `PythonByteArray.IntAPI`; this layer does not charge Python exception paths.
-/

@[expose] public section

universe v

namespace Python.Cost.ByteArray

variable {I B : Type} [PythonInt I] [PythonByteArray B]
variable {m : Type → Type v} [Monad m] [MonadCost m]

def ofBytes (B : Type) [PythonByteArray B] (bytes : PythonByteArray.Bytes B) : m B :=
  let size := PythonBytes.size bytes
  perform (.buffer {
    kind := .bytearray, op := .ofBytes, before := size, after := size,
    read := size, written := size, created := size }) (bytearray bytes)

def len (I : Type) [PythonInt I] (bytes : B) : m I :=
  perform (.buffer {
    kind := .bytearray, op := .len, before := PythonByteArray.size bytes,
    after := PythonByteArray.size bytes }) (PythonByteArray.IntAPI.len I bytes)

def get (bytes : B) (index : I) : m I :=
  perform (.buffer {
    kind := .bytearray, op := .get, args := [PythonInt.toInt index],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, read := 1 })
    (PythonByteArray.IntAPI.get bytes index)

def «repeat» (bytes : B) (count : I) : m B :=
  let result := PythonByteArray.IntAPI.repeat bytes count
  let size := PythonByteArray.size result
  perform (.buffer {
    kind := .bytearray, op := .repeat, args := [PythonInt.toInt count],
    before := PythonByteArray.size bytes, after := size, read := size, written := size,
    created := size }) result

def set (bytes : B) (index value : I) : m B :=
  perform (.buffer {
    kind := .bytearray, op := .set,
    args := [PythonInt.toInt index, PythonInt.toInt value],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, written := 1 })
    (PythonByteArray.IntAPI.set bytes index value)

def setSlice (bytes : B) (start step : I) (replacement : PythonByteArray.Bytes B)
    (hstep : 0 < PythonInt.toInt step)
    (hlen : PythonBytes.size replacement = PythonByteArray.sliceLength bytes
      (PythonInt.toNat start) (PythonInt.toNat step)) : m B :=
  perform (.buffer {
    kind := .bytearray, op := .setSlice,
    args := [PythonInt.toInt start, PythonInt.toInt step],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes,
    read := PythonBytes.size replacement, written := PythonBytes.size replacement })
    (PythonByteArray.IntAPI.setSlice bytes start step replacement hstep hlen)

def find (bytes : B) (pattern : PythonByteArray.Bytes B) (start : I)
    (hpattern : PythonBytes.size pattern = 1) : m I :=
  perform (.buffer {
    kind := .bytearray, op := .find, args := [PythonInt.toInt start],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes,
    read := PythonByteArray.IntAPI.findVisits bytes pattern start })
    (PythonByteArray.IntAPI.find bytes pattern start hpattern)

end Python.Cost.ByteArray
