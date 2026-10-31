module

public import SympyProofs.Sum.ModularShifts.Contracts
public import SympyProofs.Sum.ModularShifts.Support
public import SympyProofs.Sum.ModularShifts.Reduction
public import Std.Tactic.Do
public import Std.WP

/-! Correctness of resultant-based prime selection and lifting precision. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial
open scoped Std.WP

/-- The prime-search loop in `shifts`, isolated here for its invariant proof. -/
def firstPrimeAvoiding (lower bad : ℕ) : ℕ := Id.run do
  let bad := max 1 bad
  let mut r := lower + 1
  for candidate in [lower + 1:2 * max lower bad + 1] do
    if candidate.Prime ∧ ¬candidate ∣ bad then
      r := candidate
      break
  return r

theorem firstPrimeAvoiding_spec (lower bad : ℕ) (hb : 0 < bad) :
    (firstPrimeAvoiding lower bad).Prime ∧ lower < firstPrimeAvoiding lower bad ∧
      ¬firstPrimeAvoiding lower bad ∣ bad := by
  obtain ⟨r, hlo, hhi, hp, hn⟩ := exists_prime_in_searchRange lower bad
  have hrmem : r ∈ List.range' (lower + 1)
      (2 * max lower (max 1 bad) + 1 - (lower + 1)) := by
    rw [List.mem_range'_1]
    omega
  have hbad : max 1 bad = bad := max_eq_right (by omega)
  generalize he : firstPrimeAvoiding lower bad = result
  apply Std.WP.Id.of_run_eq_wp he
  vcgen invariants
  · fun pref _ chosen =>
      (chosen = lower + 1 ∧ ∀ s ∈ pref, ¬(s.Prime ∧ ¬s ∣ max 1 bad)) ∨
      (lower < chosen ∧ chosen.Prime ∧ ¬chosen ∣ max 1 bad)
  all_goals simp_all
  all_goals grind

/-- Avoiding the leading coefficients and precomputed derivative resultants gives
good reduction, and the lifting modulus is greater than twice the shift bound. -/
theorem precision_spec (ops : Backend) (hs : ResultantValid ops) (p q : Polynomial ℚ) (B : ℕ)
    (hp : p.Monic) (hq : q.Monic) (hps : Squarefree p) (hqs : Squarefree q)
    (hpd : p.natDegree ≠ 0) (hqd : q.natDegree ≠ 0) :
    let P := (clearDenominators p).primPart
    let Q := (clearDenominators q).primPart
    let r := firstPrimeAvoiding (max p.natDegree q.natDegree)
      (excludedDivisors ops P * excludedDivisors ops Q)
    let e := Nat.log r (2 * B) + 1
    r.Prime ∧ 0 < e ∧ max p.natDegree q.natDegree < r ∧
      2 * B < r ^ e ∧ GoodReduction r p ∧ GoodReduction r q := by
  let P := (clearDenominators p).primPart
  let Q := (clearDenominators q).primPart
  obtain ⟨hr, hdegree, hbad⟩ := firstPrimeAvoiding_spec (max p.natDegree q.natDegree)
    (excludedDivisors ops P * excludedDivisors ops Q)
    (Nat.mul_pos (excludedDivisors_pos ops hs P (primitive_separable p hp hps)
      (by simpa [P, primitive_natDegree p hp] using hpd))
      (excludedDivisors_pos ops hs Q (primitive_separable q hq hqs)
        (by simpa [Q, primitive_natDegree q hq] using hqd)))
  refine ⟨hr, Nat.succ_pos _, hdegree, Nat.lt_pow_succ_log_self hr.one_lt _, ?_, ?_⟩
  · exact goodIntegerReduction_of_resultant ops hs P hr
      (fun h => hbad (dvd_mul_of_dvd_left h _))
  · exact goodIntegerReduction_of_resultant ops hs Q hr
      (fun h => hbad (dvd_mul_of_dvd_right h _))

/-- The chosen exponent is the least positive one giving the required modulus. -/
theorem precision_exponent_minimal (r B e : ℕ)
    (he : 0 < e) (hbound : 2 * B < r ^ e) :
    Nat.log r (2 * B) + 1 ≤ e := by
  exact Nat.log_lt_of_lt_pow' (Nat.ne_of_gt he) hbound

end Gosper.ModularShifts
