module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic
public import Mathlib.Data.Int.Bitwise
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# Abstract Python integers

`PythonInt I` bundles ordinary arithmetic as a `CommRing` and comparisons as a
`LinearOrder`. A ring equivalence with `ℤ` identifies integer values; equal
mathematical values are equal in this value model. Arithmetic laws and casts
come from that equivalence rather than separate assumptions. The order agrees
with the integer order, giving the standard ordered-ring instances as well.

Lean `/` denotes Python `//` here, and `^` denotes Python `**`. Division and
remainder are specified for nonzero divisors, and powers/shifts for nonnegative
exponents/counts. Exceptions and floating-point results are outside this model.
`bitCount` counts ones in the absolute value, including for negative integers.
This interface specifies values only; it makes no runtime-cost assumptions.

Reference: https://docs.python.org/3/library/stdtypes.html#numeric-types-int-float-complex
-/

@[expose] public section

/-- Python integer operations with ordinary Lean arithmetic notation and value laws. -/
class PythonInt (I : Type) extends CommRing I, LinearOrder I, Div I, Mod I,
    Pow I I, AndOp I, ShiftLeft I, ShiftRight I where
  /-- The carrier is a copy of the integer ring, with no extra mathematical values. -/
  equivInt : I ≃+* ℤ
  /-- Python `int.bit_count()`, returning a Python integer. -/
  bitCount : I → I
  /-- Python `int.bit_length()`, excluding the sign. -/
  bitLength : I → I
  /-- Floor division rounds toward negative infinity for either sign of divisor. -/
  map_div : ∀ x y, equivInt y ≠ 0 → equivInt (x / y) = (equivInt x).fdiv (equivInt y)
  map_mod : ∀ x y, equivInt y ≠ 0 → equivInt (x % y) = (equivInt x).fmod (equivInt y)
  map_pow : ∀ x y, 0 ≤ equivInt y → equivInt (x ^ y) = equivInt x ^ (equivInt y).toNat
  map_and : ∀ x y, equivInt (x &&& y) = Int.land (equivInt x) (equivInt y)
  map_shiftLeft : ∀ x y, 0 ≤ equivInt y →
    equivInt (x <<< y) = equivInt x * 2 ^ (equivInt y).toNat
  map_shiftRight : ∀ x y, 0 ≤ equivInt y →
    equivInt (x >>> y) = (equivInt x).fdiv (2 ^ (equivInt y).toNat)
  map_bitCount : ∀ x, equivInt (bitCount x) = (Nat.digits 2 (equivInt x).natAbs).sum
  map_bitLength : ∀ x, equivInt (bitLength x) = (equivInt x).natAbs.size
  le_iff : ∀ x y, x ≤ y ↔ equivInt x ≤ equivInt y

namespace PythonInt

variable {I : Type} [PythonInt I]

/-- Observe the mathematical integer through the ring equivalence. -/
def toInt (x : I) : ℤ := equivInt x

instance : Inhabited I := ⟨0⟩

@[simp] theorem toInt_zero : toInt (0 : I) = 0 := map_zero equivInt
@[simp] theorem toInt_one : toInt (1 : I) = 1 := map_one equivInt
@[simp] theorem toInt_natCast (n : ℕ) : toInt (n : I) = n := map_natCast equivInt n
@[simp] theorem toInt_intCast (z : ℤ) : toInt (z : I) = z := map_intCast equivInt z
@[simp] theorem toInt_ofNat (n : ℕ) [n.AtLeastTwo] : toInt (ofNat(n) : I) = n :=
  map_ofNat equivInt n
@[simp] theorem toInt_add (x y : I) : toInt (x + y) = toInt x + toInt y := map_add equivInt x y
@[simp] theorem toInt_sub (x y : I) : toInt (x - y) = toInt x - toInt y := map_sub equivInt x y
@[simp] theorem toInt_neg (x : I) : toInt (-x) = -toInt x := map_neg equivInt x
@[simp] theorem toInt_mul (x y : I) : toInt (x * y) = toInt x * toInt y := map_mul equivInt x y

theorem toInt_div (x y : I) (hy : toInt y ≠ 0) :
    toInt (x / y) = (toInt x).fdiv (toInt y) := map_div x y hy
theorem toInt_mod (x y : I) (hy : toInt y ≠ 0) :
    toInt (x % y) = (toInt x).fmod (toInt y) := map_mod x y hy
theorem toInt_pow (x y : I) (hy : 0 ≤ toInt y) :
    toInt (x ^ y) = toInt x ^ (toInt y).toNat := map_pow x y hy
theorem toInt_and (x y : I) :
    toInt (x &&& y) = Int.land (toInt x) (toInt y) := map_and x y
theorem toInt_shiftLeft (x y : I) (hy : 0 ≤ toInt y) :
    toInt (x <<< y) = toInt x * 2 ^ (toInt y).toNat := map_shiftLeft x y hy
theorem toInt_shiftRight (x y : I) (hy : 0 ≤ toInt y) :
    toInt (x >>> y) = (toInt x).fdiv (2 ^ (toInt y).toNat) := map_shiftRight x y hy
@[simp] theorem toInt_bitCount (x : I) :
    toInt (bitCount x) = (Nat.digits 2 (toInt x).natAbs).sum := map_bitCount x
@[simp] theorem toInt_bitLength (x : I) :
    toInt (bitLength x) = (toInt x).natAbs.size := map_bitLength x

/-- Equality of represented values is equality in the integer carrier. -/
theorem toInt_injective : Function.Injective (toInt : I → ℤ) := equivInt.injective

@[simp] theorem toInt_eq_zero (x : I) : toInt x = 0 ↔ x = 0 := by
  rw [← toInt_zero (I := I), toInt_injective.eq_iff]

@[simp] theorem beq_iff (x y : I) : (x == y) = true ↔ toInt x = toInt y := by
  simp only [beq_iff_eq, toInt_injective.eq_iff]

@[simp] theorem lt_iff (x y : I) : x < y ↔ toInt x < toInt y := by
  simp only [lt_iff_le_not_ge, le_iff, toInt]

attribute [simp] le_iff

/-- Arithmetic and order are compatible, so standard ordered-ring lemmas apply. -/
instance : IsStrictOrderedRing I :=
  Function.Injective.isStrictOrderedRing toInt toInt_zero toInt_one toInt_add toInt_mul
    (fun {_ _} => (le_iff _ _).symm) (fun {_ _} => (lt_iff _ _).symm)

/-- Conversion at the boundary with Lean array indices and natural-number specifications.
It is lossless when the represented integer is nonnegative. -/
def toNat (x : I) : ℕ := (toInt x).toNat

@[simp] theorem toNat_natCast (n : ℕ) : toNat (n : I) = n := by simp [toNat]
@[simp] theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] : toNat (ofNat(n) : I) = n := by simp [toNat]

theorem toInt_eq_natCast (x : I) (hx : 0 ≤ toInt x) : toInt x = (toNat x : ℤ) := by
  simp [toNat, hx]

theorem bitCount_nonneg (x : I) : 0 ≤ toInt (bitCount x) := by
  rw [toInt_bitCount]
  exact Int.natCast_nonneg _
theorem bitLength_nonneg (x : I) : 0 ≤ toInt (bitLength x) := by simp

@[simp] theorem bne_iff (x y : I) : (x != y) = true ↔ toInt x ≠ toInt y := by
  simp [bne, toInt_injective.eq_iff]

/-- For nonnegative arguments the Python quotient agrees with natural division. -/
theorem toInt_div_natCast (a b : ℕ) (hb : b ≠ 0) :
    toInt ((a : I) / (b : I)) = (a / b : ℕ) := by
  rw [toInt_div _ _ (by simpa using hb), toInt_natCast, toInt_natCast, ← Int.ofNat_fdiv]

/-- Bridge used when a nonnegative loop variable is divided by a generated prime. -/
theorem toInt_div_of_nonneg (a : I) (b : ℕ) (ha : 0 ≤ toInt a) (hb : b ≠ 0) :
    toInt (a / (b : I)) = (toNat a / b : ℕ) := by
  rw [toInt_div _ _ (by simpa using hb), toInt_natCast, toInt_eq_natCast a ha,
    ← Int.ofNat_fdiv]

theorem toNat_div_of_nonneg (a : I) (b : ℕ) (ha : 0 ≤ toInt a) (hb : b ≠ 0) :
    toNat (a / (b : I)) = toNat a / b := by
  unfold toNat at *
  rw [toInt_div_of_nonneg a b ha hb, Int.toNat_natCast]
  rfl

/-- Method notation for an abstract integer carrier. -/
abbrev Value (I : Type) := I

namespace Value
abbrev toInt (x : Value I) : ℤ := PythonInt.toInt x
abbrev toNat (x : Value I) : ℕ := PythonInt.toNat x
abbrev bitCount (x : Value I) : Value I := PythonInt.bitCount x
abbrev bitLength (x : Value I) : Value I := PythonInt.bitLength x
end Value

end PythonInt
