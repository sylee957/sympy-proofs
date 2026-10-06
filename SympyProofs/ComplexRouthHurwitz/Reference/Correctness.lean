import SympyProofs.ComplexRouthHurwitz.Reference.Invariant

/-! Root-count and stability capstones for the actual direct complex table. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

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
    let s := (List.range p.natDegree).foldl
      (fun s j => Proofs.step p.natDegree j s) (Proofs.initial q p.natDegree)
    have hi := Proofs.loop_inv q p.natDegree (by omega) hqd hqm p.natDegree le_rfl
    rw [Nat.sub_self] at hi
    change Proofs.Inv q 0 s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 at hi
    have hf := hi.finish
    let axis := axisTotal s.2.2.2.2.2 s.2.2.2.2.1
    have hs := counts_C_mul p (conj p.leadingCoeff) ((_root_.map_ne_zero (starRingEnd ℂ)).mpr (leadingCoeff_ne_zero.mpr hp))
    have hr : rightCount q = rightCount p := by simpa only [q, mul_comm] using hs.1
    have ha : axisCount q = axisCount p := by simpa only [q, mul_comm] using hs.2
    have hout : s.2.2.2.2.1 = rightCount p ∧
        axis = axisCount p := by
      change s.2.2.2.2.1 = rightCount q ∧ axis = axisCount q at hf
      exact ⟨hf.1.trans hr, hf.2.trans ha⟩
    let vs := (List.range p.natDegree).foldl
      (fun s j => Proofs.vectorStep p.natDegree j s)
      (Proofs.encode (p.natDegree+1) (Proofs.initial q p.natDegree))
    have hvs : vs = Proofs.encode (p.natDegree+1) s :=
      Proofs.vector_loop_eq q p.natDegree (by omega) hqd hqm p.natDegree le_rfl
    have houtv : vs.2.2.2.2.1 = rightCount p ∧
        axisTotal vs.2.2.2.2.2 vs.2.2.2.2.1 = axisCount p := by
      rw [hvs]
      exact hout
    have hcoeff : (Vector.ofFn (fun j : Fin (p.natDegree+1) =>
        p.coeff j.val * (conj p.leadingCoeff))) = Coefficients.pack (p.natDegree+1) q := by
      apply Vector.ext; intro j hj
      simp [Coefficients.pack, q]
    simp only [run, ite_eq_right hn, hcoeff, Coefficients.scan_pack q p.natDegree]
    simp only [← apply_ite (fun s : Proofs.VectorLocals (p.natDegree+1) =>
      (pure (ForInStep.yield s) : Id _)), List.forIn_pure_yield_eq_foldl]
    simpa only [vs, Proofs.vectorStep, Proofs.encode, Proofs.initial,
      List.map_nil, pure_bind, Id.run_pure] using houtv

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
