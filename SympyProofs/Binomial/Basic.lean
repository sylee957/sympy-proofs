module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic

/-!
# SymPy's binomial convention with an integer lower argument

Mathlib's `Ring.choose : R → ℕ → R` already has the required polynomial
interpretation, including negative upper integers. The only new convention here
is extension by zero to negative lower integers. In particular, this is not the
reflection-symmetric convention at negative upper integers.

The definition is generic: use `R = ℤ` for the exact integer function and `R = ℂ`
for its polynomial extension in the upper argument with the lower integer fixed.
-/

@[expose] public section

namespace SympyBinomial

section Ring

variable {R : Type*} [Ring R] [BinomialRing R]

/-- SymPy's binomial for an integer lower argument, extending mathlib by zero. -/
def choose (z : R) (k : ℤ) : R :=
  if k < 0 then 0 else Ring.choose z k.toNat

@[simp]
theorem choose_of_neg (z : R) {k : ℤ} (hk : k < 0) : choose z k = 0 := by
  simp [choose, hk]

theorem choose_of_nonneg (z : R) {k : ℤ} (hk : 0 ≤ k) :
    choose z k = Ring.choose z k.toNat := by
  simp [choose, not_lt.mpr hk]

/-- The nonnegative lower-argument case is exactly mathlib, not a new definition. -/
@[simp]
theorem choose_natCast (z : R) (k : ℕ) : choose z (k : ℤ) = Ring.choose z k := by
  simp [choose]

@[simp]
theorem choose_zero (z : R) : choose z 0 = 1 := by
  simpa using choose_natCast z 0 |>.trans (Ring.choose_zero_right z)

@[simp]
theorem choose_one (z : R) : choose z 1 = z := by
  simpa using choose_natCast z 1 |>.trans (Ring.choose_one_right z)

/-- Agreement with ordinary natural binomial coefficients, including `k > n`. -/
@[simp]
theorem choose_natCast_natCast (n k : ℕ) :
    choose (n : R) (k : ℤ) = (n.choose k : R) := by
  rw [choose_natCast, Ring.choose_natCast]

theorem choose_natCast_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    choose (n : R) (k : ℤ) = 0 := by
  rw [choose_natCast_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-- Reflection symmetry in the ordinary natural triangular range. -/
theorem choose_natCast_symm {n k : ℕ} (hk : k ≤ n) :
    choose (n : R) ((n - k : ℕ) : ℤ) = choose (n : R) (k : ℤ) := by
  rw [choose_natCast_natCast, choose_natCast_natCast, Nat.choose_symm hk]

/-- Pascal's recurrence, including both negative lower-argument boundary cases. -/
theorem choose_add_one_add_one (z : R) (k : ℤ) :
    choose (z + 1) (k + 1) = choose z k + choose z (k + 1) := by
  cases k with
  | ofNat k =>
    change choose (z + 1) ((k : ℤ) + 1) = choose z (k : ℤ) + choose z ((k : ℤ) + 1)
    simpa only [← Nat.cast_add_one, choose_natCast] using Ring.choose_succ_succ z k
  | negSucc k =>
    cases k with
    | zero => simp [choose]
    | succ k =>
      have h₂ : Int.negSucc (k + 1) + 1 < 0 := by omega
      simp [choose_of_neg _ h₂]

/-- The usual form of Pascal's identity holds on the entire integer lattice. -/
theorem choose_pascal (z : R) (k : ℤ) :
    choose z k = choose (z - 1) k + choose (z - 1) (k - 1) := by
  simpa [add_comm] using choose_add_one_add_one (z - 1) (k - 1)

/-- Negating the upper argument gives the usual signed polynomial identity. -/
theorem choose_neg (z : R) (k : ℕ) :
    choose (-z) (k : ℤ) = (-1 : R) ^ k * choose (z + k - 1) (k : ℤ) := by
  simp only [choose_natCast, Ring.choose_neg, Units.smul_def, zsmul_eq_mul,
    Int.coe_negOnePow_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- For `n = -(m+1)`, reduce to a natural binomial and a parity sign. -/
theorem choose_neg_natCast_succ (m k : ℕ) :
    choose (-((m : R) + 1)) (k : ℤ) = (-1 : R) ^ k * ((m + k).choose k : R) := by
  rw [choose_neg]
  have h : (m : R) + 1 + k - 1 = ((m + k : ℕ) : R) := by
    simp [Nat.cast_add, add_sub_assoc]
  rw [h, choose_natCast_natCast]

@[simp]
theorem choose_neg_one (k : ℕ) : choose (-1 : R) (k : ℤ) = (-1 : R) ^ k := by
  simpa using choose_neg_natCast_succ (R := R) 0 k

/-- Casting integer binomials into any binomial ring preserves the convention. -/
theorem intCast_choose (n k : ℤ) : ((choose n k : ℤ) : R) = choose (n : R) k := by
  by_cases hk : k < 0
  · simp [choose_of_neg _ hk]
  · simpa [choose, hk] using
      Ring.map_choose (Int.castRingHom R) n k.toNat

end Ring

section Field

variable {R : Type*} [Field R] [CharZero R]

/-- Falling-factorial form of the polynomial binomial. -/
theorem choose_eq_descPochhammer (z : R) (k : ℕ) :
    choose z (k : ℤ) = (descPochhammer R k).eval z / (k.factorial : R) := by
  rw [choose_natCast, Ring.choose_eq_smul]
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The finite-product definition valid for every upper argument in characteristic zero. -/
theorem choose_eq_prod (z : R) (k : ℕ) :
    choose z (k : ℤ) = (∏ j ∈ Finset.range k, (z - j)) / (k.factorial : R) := by
  rw [choose_eq_descPochhammer, descPochhammer_eval_eq_prod_range]

end Field

/-- Explicit all-integer specification matching SymPy's three cases. -/
theorem choose_int_eq (n k : ℤ) :
    choose n k =
      if k < 0 then 0
      else if 0 ≤ n then (n.toNat.choose k.toNat : ℤ)
      else (-1 : ℤ) ^ k.toNat * ((k - n - 1).toNat.choose k.toNat : ℤ) := by
  by_cases hk : k < 0
  · simp [hk]
  have hk0 : 0 ≤ k := le_of_not_gt hk
  lift k to ℕ using hk0 with k
  cases n with
  | ofNat n => simp [Ring.choose_natCast]
  | negSucc m =>
    have ht : ((k : ℤ) - Int.negSucc m - 1).toNat = m + k := by omega
    simp only [not_lt.mpr (Int.natCast_nonneg k), ↓reduceIte,
      Int.negSucc_not_nonneg, Int.toNat_natCast, ht]
    simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using
      choose_neg_natCast_succ (R := ℤ) m k

/-- Negative upper arguments prevent global reflection symmetry under SymPy's convention. -/
theorem reflection_fails : choose (-1 : ℤ) 0 ≠ choose (-1 : ℤ) (-1 - 0) := by
  simp [choose]

end SympyBinomial
