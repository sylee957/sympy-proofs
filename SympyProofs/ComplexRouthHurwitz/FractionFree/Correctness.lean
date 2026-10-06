import SympyProofs.ComplexRouthHurwitz.FractionFree.Invariant

/-! Root-count and stability capstones for the previous-squared-pivot field model. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

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
    let s := (List.range p.natDegree).foldl
      (fun s j => ProofsFF.step p.natDegree j s) (ProofsFF.initial q p.natDegree)
    have hi := ProofsFF.loop_valid q p.natDegree (by omega) hqd hqm p.natDegree le_rfl
    rw [Nat.sub_self] at hi
    have hf := ProofsFF.finish hi
    let axis := axisTotal s.2.2.2.2.2.1 s.2.2.2.2.1
    have hs := counts_C_mul p (phase p.leadingCoeff) (phase_ne_zero _)
    have hr : rightCount q = rightCount p := hs.1
    have ha : axisCount q = axisCount p := hs.2
    have hout : s.2.2.2.2.1 = rightCount p ∧
        axis = axisCount p := by
      change s.2.2.2.2.1 = rightCount q ∧ axis = axisCount q at hf
      exact ⟨hf.1.trans hr, hf.2.trans ha⟩
    have hcoeff : (Vector.ofFn (fun j : Fin (p.natDegree+1) =>
        phase p.leadingCoeff * p.coeff j.val)) = Coefficients.pack (p.natDegree+1) q := by
      apply Vector.ext; intro j hj
      simp [Coefficients.pack, q]
    simp only [runFF, ite_eq_right hn, hcoeff]
    simp only [← apply_ite (fun s : ProofsFF.Locals (p.natDegree+1) =>
      (pure (ForInStep.yield s) : Id _)), List.forIn_pure_yield_eq_foldl]
    simpa only [s, axis, ProofsFF.step, ProofsFF.initial, pure_bind, Id.run_pure] using hout

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
