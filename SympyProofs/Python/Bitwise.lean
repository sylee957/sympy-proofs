module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic
public import Std.Tactic.Do
public import Std.WP

/-!
# Python bit operations on nonnegative integers

Unbounded `Nat` arithmetic models the nonnegative inputs used by the algorithms.
The shift and low-bit theorems identify Lean's bit operations with multiplication,
floor division, and remainder by powers of two. The bit-count loop is proved to
compute the sum of binary digits, the specification of Python's `int.bit_count`
on this domain. Signed inputs and negative shift counts are outside this model.
-/

@[expose] public section

namespace Python.Bitwise

open scoped Std.WP

/-- Public bit operations implementing Python's nonnegative `int.bit_count`. -/
def bitCount (n : ℕ) : ℕ := Id.run do
  let mut x := n
  let mut count := 0
  for _ in [:n.size] do
    count := count + (x &&& 1)
    x := x >>> 1
  return count

private theorem digits_step (n : ℕ) :
    (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n / 2)).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_def' (by decide) (by omega), List.sum_cons]

/-- The bitwise loop computes the sum of binary digits, i.e. Python's bit count. -/
theorem bitCount_eq_digit_sum (n : ℕ) : bitCount n = (Nat.digits 2 n).sum := by
  generalize he : bitCount n = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ (x, count) =>
      x = n / 2 ^ pref.length ∧ count + (Nat.digits 2 x).sum = (Nat.digits 2 n).sum
  case vc1 => simp
  case vc2 =>
    rename_i x count hinv
    have hx : x = 0 := by
      simpa [Nat.div_eq_of_lt (Nat.lt_size_self n)] using hinv.1
    simpa [hx] using hinv.2
  case vc3 =>
    rename_i pref i suff hs x count hinv
    simp +zetaDelta only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one]
    constructor
    · simp [hinv.1, Nat.div_div_eq_div_mul, pow_succ]
    · rw [Nat.add_assoc, ← digits_step, hinv.2]

/-- A left shift restores precisely a power of two. -/
theorem shiftLeft_eq (odd exponent : ℕ) : odd <<< exponent = odd * 2 ^ exponent :=
  Nat.shiftLeft_eq_mul_pow odd exponent

/-- Right shift has Python's floor-division semantics on nonnegative inputs. -/
theorem shiftRight_eq (n count : ℕ) : n >>> count = n / 2 ^ count :=
  Nat.shiftRight_eq_div_pow n count

/-- Masking with one selects the remainder modulo two. -/
theorem andOne_eq (n : ℕ) : n &&& 1 = n % 2 :=
  Nat.and_one_is_mod n

/-- Binary length is a sufficient bound for every repeated prime-division loop. -/
theorem div_pow_size_eq_zero (n p : ℕ) (hp : 2 ≤ p) : n / p ^ n.size = 0 := by
  apply Nat.div_eq_of_lt
  exact (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_left hp n.size)

end Python.Bitwise
