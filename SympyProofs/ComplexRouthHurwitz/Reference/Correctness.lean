import SympyProofs.ComplexRouthHurwitz.Reference.Invariant
import SympyProofs.RouthHurwitz.Imperative.Basic
import Std.Tactic.Do
import Std.WP

/-! Root-count and stability capstones for the actual direct complex table. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

open scoped Std.WP in
/-- The direct table counts roots in the open right half-plane and on the
imaginary axis, with multiplicity, including all exceptional repair branches. -/
theorem run_counts_correct (p : ℂ[X]) (hp : p ≠ 0) :
    (run p).rightRoots = rightCount p ∧
      (run p).axisRoots = axisCount p := by
  by_cases hn : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hn
    simp only [run, ite_eq_left hn]
    rw [he]
    simp [rightCount, axisCount, regionCount]
  · let q := p * C (conj p.leadingCoeff)
    have hqd : q.natDegree = p.natDegree :=
      natDegree_mul_C ((_root_.map_ne_zero (starRingEnd ℂ)).mpr (leadingCoeff_ne_zero.mpr hp))
    have hqm : PositiveLeading q := by
      simp only [PositiveLeading, q, leadingCoeff_mul, leadingCoeff_C, Complex.mul_conj,
        Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨by simp, Complex.normSq_pos.mpr (leadingCoeff_ne_zero.mpr hp)⟩
    have hs : rightCount q = rightCount p ∧ axisCount q = axisCount p := by
      simpa only [q, mul_comm] using counts_C_mul p (conj p.leadingCoeff)
        ((_root_.map_ne_zero (starRingEnd ℂ)).mpr (leadingCoeff_ne_zero.mpr hp))
    have hcoeff : (Vector.ofFn (fun j : Fin (p.natDegree+1) =>
        p.coeff j.val * conj p.leadingCoeff)) = Coefficients.pack (p.natDegree+1) q := by
      apply Vector.ext; intro j hj
      simp [Coefficients.pack, q]
    generalize h : run p = result
    apply Std.WP.Id.of_run_eq_wp h
    vcgen invariants
    · fun pref _ s => ∃ t : Proofs.Locals,
        Proofs.atLocals q (p.natDegree-pref.length) t ∧ s = Proofs.encode (p.natDegree+1) t
    case vc1 => exact (hn ‹_ = 0›).elim
    case vc2 =>
      refine ⟨Proofs.initial q p.natDegree, ?_, ?_⟩
      · simpa only [List.length_nil, Nat.sub_zero] using
          Proofs.initial_inv q p.natDegree (by omega) hqd hqm
      · simp +zetaDelta only [hcoeff, Coefficients.scan_pack, Proofs.encode, Proofs.initial,
        List.map_nil]
    case vc3 =>
      obtain ⟨t, hi, he⟩ := ‹∃ t : Proofs.Locals, _›
      simp +zetaDelta only [List.length_range, Nat.sub_self] at hi
      have hf := hi.finish
      have hc := congrArg (fun s : Proofs.VectorLocals (p.natDegree+1) => s.2.2.2.2.1) he
      have ha := congrArg (fun s : Proofs.VectorLocals (p.natDegree+1) =>
        axisTotal s.2.2.2.2.2 s.2.2.2.2.1) he
      exact ⟨hc.trans (hf.1.trans hs.1), ha.trans (hf.2.trans hs.2)⟩
    case vc4 | vc5 =>
      rename_i pref k suff hsplit u v rs ps c aux hi _ _ _ _ hbranch
      obtain ⟨hk, hlt⟩ := Imperative.Bounds.range_split hsplit
      obtain ⟨t, ht, he⟩ := hi
      rw [← hk] at ht
      have heq : Proofs.vectorStep p.natDegree k (u, v, rs, ps, c, aux) =
          Proofs.encode (p.natDegree+1) (Proofs.step p.natDegree k t) := by
        rw [he]
        exact Proofs.vectorStep_encode q p.natDegree k hlt t ht
      refine ⟨Proofs.step p.natDegree k t, ?_, ?_⟩
      · simpa only [List.length_append, List.length_singleton, ← hk] using
          Proofs.step_inv q p.natDegree k hlt t ht
      · dsimp only [d, n] at hbranch
        simpa +zetaDelta only [Proofs.vectorStep, hbranch, ite_true, ite_false] using heq

/-- Acceptance is exactly strict Hurwitz stability for nonzero complex polynomials. -/
theorem run_stable_iff (p : ℂ[X]) (hp : p ≠ 0) :
    (run p).stable = true ↔ ComplexStable p := by
  have hs := run_counts_correct p hp
  have he : (run p).stable = decide ((run p).rightRoots = 0 ∧ (run p).axisRoots = 0) := by
    by_cases hn : p.natDegree = 0
    · simp [run, hn]
    · simp only [run, ite_eq_right hn]
      rfl
  rw [he, decide_eq_true_eq, hs.1, hs.2, complexStable_iff_counts p hp]

end
end RouthHurwitz.ComplexRouth
