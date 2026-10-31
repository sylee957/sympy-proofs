module

public import Mathlib

/-! Existence of a suitable prime, used to justify the search in `Algorithm`. -/

@[expose] public section
namespace Gosper.ModularShifts

/-- The bounded search contains a prime above the degree bound that avoids the
excluded integer. `max 1 bad` also makes the search total when `bad = 0`. -/
theorem exists_prime_in_searchRange (lower bad : ℕ) :
    ∃ r, lower < r ∧ r < 2 * max lower (max 1 bad) + 1 ∧
      r.Prime ∧ ¬r ∣ max 1 bad := by
  let n := max lower (max 1 bad)
  obtain ⟨r, hr, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul n (by dsimp [n]; omega)
  refine ⟨r, by dsimp [n] at hlo; omega, by dsimp [n] at hhi; omega, hr, ?_⟩
  intro hd
  have hle := Nat.le_of_dvd (by omega : 0 < max 1 bad) hd
  dsimp [n] at hlo
  omega

end Gosper.ModularShifts
