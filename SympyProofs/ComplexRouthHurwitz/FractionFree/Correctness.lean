import SympyProofs.ComplexRouthHurwitz.FractionFree.Invariant
import SympyProofs.RouthHurwitz.Imperative.Basic
import Std.Tactic.Do
import Std.WP

/-! Root-count and stability capstones for the previous-squared-pivot field model. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

open scoped Std.WP in
/-- The direct table counts roots in the open right half-plane and on the
imaginary axis, with multiplicity, including all exceptional repair branches. -/
theorem runFF_counts_correct (p : ℂ[X]) (hp : p ≠ 0) :
    (runFF p).rightRoots = rightCount p ∧
      (runFF p).axisRoots = axisCount p := by
  by_cases hn : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hn
    simp only [runFF, ite_eq_left hn]
    rw [he]
    simp [rightCount, axisCount, regionCount]
  · let q := C (phase p.leadingCoeff)*p
    have hqd : q.natDegree = p.natDegree := natDegree_C_mul (phase_ne_zero _)
    have hqm : 0 < q.leadingCoeff.re := by
      simp only [q, leadingCoeff_mul, leadingCoeff_C]
      exact phase_re_pos _ (leadingCoeff_ne_zero.mpr hp)
    have hs := counts_C_mul p (phase p.leadingCoeff) (phase_ne_zero _)
    have hcoeff : (Vector.ofFn (fun j : Fin (p.natDegree+1) =>
        phase p.leadingCoeff * p.coeff j.val)) = Coefficients.pack (p.natDegree+1) q := by
      apply Vector.ext; intro j hj
      simp [Coefficients.pack, q]
    generalize h : runFF p = result
    apply Std.WP.Id.of_run_eq_wp h
    vcgen invariants
    · fun pref _ s => ProofsFF.Valid q (p.natDegree-pref.length) s
    case vc1 => exact (hn ‹_ = 0›).elim
    case vc2 =>
      simpa +zetaDelta only [List.length_nil, Nat.sub_zero, hcoeff, ProofsFF.initial] using
        ProofsFF.initial_valid q p.natDegree (by omega) hqd hqm
    case vc3 =>
      have hi := ‹ProofsFF.Valid q _ _›
      simp +zetaDelta only [List.length_range, Nat.sub_self] at hi
      simpa only [hs.1, hs.2] using ProofsFF.finish hi
    case vc4 | vc5 =>
      rename_i pref k suff hsplit u v rs ps c aux div hi _ _ _ _ _ _ _ hbranch
      obtain ⟨hk, hlt⟩ := Imperative.Bounds.range_split hsplit
      have hnext := ProofsFF.step_valid q p.natDegree k hlt (u, v, rs, ps, c, aux, div)
        (hk.symm ▸ hi)
      dsimp only [d, n] at hbranch
      simpa +zetaDelta only [ProofsFF.step, List.length_append, List.length_singleton,
        ← hk, hbranch, ite_true, ite_false] using hnext

/-- Acceptance is exactly strict Hurwitz stability for nonzero complex polynomials. -/
theorem runFF_stable_iff (p : ℂ[X]) (hp : p ≠ 0) :
    (runFF p).stable = true ↔ ComplexStable p := by
  have hs := runFF_counts_correct p hp
  have he : (runFF p).stable = decide ((runFF p).rightRoots = 0 ∧ (runFF p).axisRoots = 0) := by
    by_cases hn : p.natDegree = 0
    · simp [runFF, hn]
    · simp only [runFF, ite_eq_right hn]
      rfl
  rw [he, decide_eq_true_eq, hs.1, hs.2, complexStable_iff_counts p hp]

end
end RouthHurwitz.ComplexRouth.FractionFree
