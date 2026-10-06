import SympyProofs.ComplexRouthHurwitz.Exact.Invariant

/-! Root counts, strict stability, and exact integer division for the compressed runner. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial Model

/-- Exact right-half-plane and imaginary-axis root counts, with multiplicity. -/
theorem run_counts_correct (p : GaussianInt[X]) (hp : p≠0) :
    (run p).rightRoots=rightCount (denote p) ∧ (run p).axisRoots=axisCount (denote p) := by
  classical
  by_cases hn : p.natDegree=0
  · have he := eq_C_of_natDegree_eq_zero hn
    simp only [run, ite_eq_left hn]
    rw [he]
    simp [denote, rightCount, axisCount, regionCount]
  · obtain ⟨hc,hd,hq⟩ := Proofs.input_spec p hp
    obtain ⟨t,ht,hr⟩ := Proofs.loop_valid (Proofs.rotated p) p.natDegree (Proofs.input p)
      (by omega) hd hq hc p.natDegree le_rfl
    rw [Nat.sub_self] at ht
    have hf := FractionFree.ProofsFF.finish ht.1
    have hs := Proofs.rotated_counts p
    have hout := And.intro (hr.2.2.2.1.trans (hf.1.trans hs.1))
      ((congrArg₂ axisTotal hr.2.2.2.2.1 hr.2.2.2.1).trans (hf.2.trans hs.2))
    have hnlt : p.natDegree < p.natDegree+1 := by omega
    by_cases hz : ((Proofs.input p)[p.natDegree]).im = 0
    all_goals simp only [Proofs.input] at hz
    all_goals simp only [run, ite_eq_right hn, hz, ne_eq, not_true_eq_false,
      not_false_eq_true, ↓reduceIte]
    all_goals simp only [← apply_ite (fun s : Proofs.Locals (p.natDegree+1) =>
      (pure (ForInStep.yield s) : Id _)), List.forIn_pure_yield_eq_foldl]
    all_goals simpa only [Proofs.step, Proofs.initial, Proofs.input, initialRows,
      initialDivisor, Rows.entry, dite_eq_left hnlt, hz, ↓reduceIte, pure_bind, Id.run_pure] using hout

/-- Acceptance is equivalent to strict Hurwitz stability of the complex denotation. -/
theorem run_stable_iff (p : GaussianInt[X]) (hp : p≠0) :
    (run p).stable=true ↔ ComplexStable (denote p) := by
  classical
  have hs := run_counts_correct p hp
  have he : (run p).stable=decide ((run p).rightRoots=0 ∧ (run p).axisRoots=0) := by
    by_cases hn : p.natDegree=0
    · simp [run,hn]
    · by_cases hz : ((Proofs.input p)[p.natDegree]).im = 0
      all_goals simp only [Proofs.input] at hz
      all_goals simp only [run, ite_eq_right hn, hz, ne_eq, not_true_eq_false,
        not_false_eq_true, ↓reduceIte]
      all_goals rfl
  rw [he, decide_eq_true_eq, hs.1,hs.2,complexStable_iff_counts _ (denote_ne_zero p hp)]


/-- Every integer division performed by the compressed loop is exact. -/
theorem run_divisions_exact (p : GaussianInt[X]) (hp : p≠0) (k : ℕ)
    (hk : k < p.natDegree) (hd : p.natDegree-(k+1)≠0) :
    let n := p.natDegree
    let s := (List.range k).foldl (fun s j => Proofs.step n j s) (Proofs.initial (Proofs.input p) n)
    let d := n-(k+1)
    let r := repair d s.1 s.2.1
    let D := if entry s.2.1 d=0 then 1 else s.2.2.2.2.2.2
    0 < D ∧ ∀ j : Fin (n+1), D ∣ numerator d r.upper r.lower j := by
  classical
  obtain ⟨hc,hn,hq⟩ := Proofs.input_spec p hp
  let n := p.natDegree
  let s := (List.range k).foldl (fun s j => Proofs.step n j s) (Proofs.initial (Proofs.input p) n)
  let d := n-(k+1)
  obtain ⟨t,hv,hr⟩ := Proofs.loop_valid (Proofs.rotated p) n (Proofs.input p)
    (by omega) hn hq hc k (by omega)
  have hu : decode (d+1) s.1=t.1 := by simpa only [show n-k=d+1 by dsimp [d]; omega] using hr.1
  have hl : decode d s.2.1=t.2.1 := by
    simpa only [show n-k-1=d by dsimp [d]; omega] using hr.2.1
  have hD : (if entry s.2.1 d=0 then 1 else s.2.2.2.2.2.2) =
      (if (Rows.entry t.2.1 d).re=0 then 1 else t.2.2.2.2.2.2) := by
    rw [← hl, decode_pivot, hr.2.2.2.2.2]
  have hrs := repair_spec d s.1 s.2.1
  rw [hu,hl] at hrs
  have hloss := Proofs.repaired_rows (Proofs.rotated p) n k t hk hv
  have hru : decode (d+1) (repair d s.1 s.2.1).upper = (Rows.repair d t.1 t.2.1).upper := by
    rw [hrs.1]; exact hloss.1
  have hrl : decode d (repair d s.1 s.2.1).lower = (Rows.repair d t.1 t.2.1).lower := by
    rw [hrs.2]; exact hloss.2
  have ready := ProofsG.step_ready (Proofs.rotated p) n k hk t hv
  have he : 0 < (if (Rows.entry t.2.1 d).re=0 then 1 else t.2.2.2.2.2.2 : ℤ) ∧
      ∀ j : Fin (n+1), ((if (Rows.entry t.2.1 d).re=0 then 1 else t.2.2.2.2.2.2 : ℤ):GaussianInt) ∣
        cellNumerator d (Rows.repair d t.1 t.2.1).upper (Rows.repair d t.1 t.2.1).lower j := by
    constructor
    · exact_mod_cast ready.1
    · intro j
      apply cell_divides
      · exact_mod_cast (ne_of_gt ready.1)
      · exact (ready.2 hd).1
  change 0 < _ ∧ ∀ j : Fin (n+1), _ ∣ numerator d (repair d s.1 s.2.1).upper (repair d s.1 s.2.1).lower j
  rw [hD]
  refine ⟨he.1, ?_⟩
  intro j
  rw [numerator_spec d (by dsimp [d,n]; omega), hru, hrl]
  obtain ⟨z,hz⟩ := he.2 j
  change cellNumerator d (Rows.repair d t.1 t.2.1).upper (Rows.repair d t.1 t.2.1).lower j =
    ((if (Rows.entry t.2.1 d).re=0 then 1 else t.2.2.2.2.2.2 : ℤ):GaussianInt)*z at hz
  rw [hz]
  by_cases hj : (d-1)%2=j.val%2
  · simp only [hj, ite_true]; exact ⟨z.re, by split_ifs <;> simp⟩
  · simp only [hj, ite_false]; exact ⟨z.im, by split_ifs <;> simp⟩


end RouthHurwitz.ComplexRouth.Exact.Gaussian
