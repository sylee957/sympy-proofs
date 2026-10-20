module

public import SympyProofs.Python.Cost.Index
public import SympyProofs.Python.ByteArray

/-!
# Cost adapters for the verified sieve's storage indices

These are the natural-index counterparts of the PythonInt-facing byte APIs.
The guarded slice assignment agrees with Python on positive-stride equal-length
slices. An invalid call returns the input unchanged; no Python exception path
is modeled. Using this adapter in a cost proof requires showing that its calls
are valid; the original sieve's correctness theorem alone does not establish
equivalence of the separate instrumented program.
-/

@[expose] public section

universe v

namespace Python.Cost.BufferIndex

variable {B : Type} [PythonByteArray B]
variable {m : Type → Type v} [Monad m] [MonadCost m]

def literal (B : Type) [PythonByteArray B] (value : UInt8) : m (PythonByteArray.Bytes B) :=
  perform (.buffer { kind := .bytes, op := .literal, after := 1, written := 1, created := 1 })
    (PythonBytes.literal #[value])

def ofBytes (bytes : PythonByteArray.Bytes B) : m B :=
  let size := PythonBytes.size bytes
  perform (.buffer {
    kind := .bytearray, op := .ofBytes, before := size, after := size,
    read := size, written := size, created := size }) (bytearray bytes)

def repeatArray (bytes : B) (count : ℕ) : m B :=
  let size := PythonByteArray.size bytes * count
  perform (.buffer {
    kind := .bytearray, op := .repeat, args := [count], before := PythonByteArray.size bytes,
    after := size, read := size, written := size, created := size }) (bytes * count)

def repeatBytes (B : Type) [PythonByteArray B] (bytes : PythonByteArray.Bytes B)
    (count : ℤ) : m (PythonByteArray.Bytes B) :=
  let size := PythonBytes.size bytes * count.toNat
  perform (.buffer {
    kind := .bytes, op := .repeat, args := [count], before := PythonBytes.size bytes,
    after := size, read := size, written := size, created := size }) (bytes * count)

def length (bytes : B) : m ℤ :=
  perform (.buffer {
    kind := .bytearray, op := .len, before := PythonByteArray.size bytes,
    after := PythonByteArray.size bytes }) (PythonByteArray.len bytes)

def get (bytes : B) (i : ℕ) : m UInt8 :=
  perform (.buffer {
    kind := .bytearray, op := .get, args := [i], before := PythonByteArray.size bytes,
    after := PythonByteArray.size bytes, read := 1 }) bytes[i]!

def set (bytes : B) (i : ℕ) (value : UInt8) : m B :=
  perform (.buffer {
    kind := .bytearray, op := .set, args := [i, value.toNat],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, written := 1 })
    (PythonByteArray.set! bytes i value)

def setSlice (bytes : B) (start step : ℕ) (replacement : PythonByteArray.Bytes B) : m B :=
  let result := if hs : 0 < step then
    if hl : PythonBytes.size replacement = PythonByteArray.sliceLength bytes start step then
      PythonByteArray.setSlice bytes start step replacement hs hl
    else bytes
  else bytes
  perform (.buffer {
    kind := .bytearray, op := .setSlice, args := [start, step],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes,
    read := PythonBytes.size replacement, written := PythonBytes.size replacement }) result

def find (bytes : B) (value : UInt8) (start : ℕ) : m ℤ :=
  let result := PythonByteArray.find bytes value start
  let visits := if result = -1 then PythonByteArray.size bytes - start
    else result.toNat + 1 - start
  perform (.buffer {
    kind := .bytearray, op := .find, args := [start],
    before := PythonByteArray.size bytes, after := PythonByteArray.size bytes, read := visits }) result

end Python.Cost.BufferIndex
