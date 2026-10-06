import SympyProofs.RouthHurwitz.FractionFree.Invariant

/-! Root-count and stability correctness obtained from initialization,
preservation, and termination of the actual imperative loop. -/
namespace RouthHurwitz.FractionFree
open Polynomial Imperative Proofs

private theorem run_outcome (p : Polynomial ℝ) (hp : p ≠ 0) :
    (Exact.run p).signChanges = rightCount (p.map Complex.ofRealHom) ∧
      (((Exact.run p).degenerate = false ∧ (Exact.run p).signChanges = 0) ↔ HurwitzStable p) := by
  by_cases hn : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hn
    have hc : p.coeff 0 ≠ 0 := by
      simpa [Polynomial.leadingCoeff, hn] using leadingCoeff_ne_zero.mpr hp
    have hs : HurwitzStable p := by
      intro z hz
      rw [he] at hz
      simp only [Polynomial.map_C, eval_C] at hz
      change (p.coeff 0 : ℂ) = 0 at hz
      exact (hc (Complex.ofReal_eq_zero.mp hz)).elim
    have hr : rightCount (p.map Complex.ofRealHom) = 0 := by rw [he]; simp
    simp [Exact.Proofs.run_eq, hn, hc, hr, hs]
  · have hi := loop_invariant p hp (p.natDegree-1) (by omega)
    obtain ⟨u, v, _, _, hm, _, _⟩ := hi
    rw [show p.natDegree - (p.natDegree-1+1) = 0 by omega] at hm
    have hend := hm.finish hp
    simp only [Exact.Proofs.run_eq, ite_eq_right hn]
    exact hend

/-- The stored counter counts open-right-half-plane roots with multiplicity. -/
theorem real_run_signChanges_correct (p : Polynomial ℝ) (hp : p ≠ 0) :
    (Exact.run p).signChanges = rightCount (p.map Complex.ofRealHom) :=
  (run_outcome p hp).1

/-- Acceptance is equivalent to strict stability, including rejection of zero. -/
theorem accepts_real_run_iff_hurwitzStable (p : Polynomial ℝ) :
    accepts (Exact.run p) = true ↔ HurwitzStable p := by
  by_cases hp : p = 0
  · subst p
    simp [Exact.Proofs.run_eq, accepts, HurwitzStable]
    exact ⟨0, by simp⟩
  · simpa only [accepts, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq]
      using (run_outcome p hp).2

end RouthHurwitz.FractionFree
