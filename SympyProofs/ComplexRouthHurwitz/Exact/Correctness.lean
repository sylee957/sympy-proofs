import SympyProofs.ComplexRouthHurwitz.Exact.Invariant

/-! Root-count and stability capstones for the Gaussian-integer runner. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

namespace ProofsG

def input (p : GaussianInt[X]) : Rows.Row (p.natDegree+1) :=
  Vector.ofFn (fun j => phase p.leadingCoeff * p.coeff j.val)

def rotated (p : GaussianInt[X]) : ℂ[X] :=
  C (FractionFree.phase (denote p).leadingCoeff) * denote p

theorem input_spec (p : GaussianInt[X]) (hp : p ≠ 0) :
    mapRow (input p) = Coefficients.pack (p.natDegree+1) (rotated p) ∧
    (rotated p).natDegree = p.natDegree ∧ 0 < (rotated p).leadingCoeff.re := by
  have hpn := denote_ne_zero p hp
  constructor
  · apply Vector.ext; intro j hj
    simp only [input, mapRow, Coefficients.pack, rotated, coeff_C_mul, denote, coeff_map,
      Fin.getElem_fin, Vector.getElem_ofFn, map_mul, map_phase]
    rw [Polynomial.leadingCoeff_map_of_injective GaussianInt.toComplex_injective]
  constructor
  · rw [rotated, natDegree_C_mul (FractionFree.phase_ne_zero _), denote_natDegree]
  · simp only [rotated, leadingCoeff_mul, leadingCoeff_C]
    exact FractionFree.phase_re_pos _ (leadingCoeff_ne_zero.mpr hpn)

theorem rotated_counts (p : GaussianInt[X]) :
    rightCount (rotated p) = rightCount (denote p) ∧
    axisCount (rotated p) = axisCount (denote p) :=
  counts_C_mul _ _ (FractionFree.phase_ne_zero _)
end ProofsG

/-- Every division actually performed by the loop has a positive integer divisor
and a Gaussian-integer quotient. The last iteration performs no division. -/
theorem run_divisions_exact (p : GaussianInt[X]) (hp : p ≠ 0) (k : ℕ)
    (hk : k < p.natDegree) (hd : p.natDegree-(k+1) ≠ 0) :
    let n := p.natDegree
    let s := (List.range k).foldl (fun s j => ProofsG.step n j s) (ProofsG.initial (ProofsG.input p) n)
    let d := n-(k+1)
    let r := Rows.repair d s.1 s.2.1
    let D : ℤ := if (Rows.entry s.2.1 d).re=0 then 1 else s.2.2.2.2.2.2
    0 < D ∧ ∀ j : Fin (n+1), (D:GaussianInt) ∣ cellNumerator d r.upper r.lower j := by
  obtain ⟨hc,hn,hq⟩ := ProofsG.input_spec p hp
  have hi := ProofsG.loop_valid (ProofsG.rotated p) p.natDegree (ProofsG.input p)
    (by omega) hn hq hc k (by omega)
  have hr := ProofsG.step_ready _ _ _ hk _ hi
  constructor
  · exact_mod_cast hr.1
  · intro j
    apply cell_divides
    · exact_mod_cast (ne_of_gt hr.1)
    · exact (hr.2 hd).1

/-- The integer computation counts roots of the input's complex denotation,
with multiplicity, including all exceptional repair branches. -/
theorem run_counts_correct (p : GaussianInt[X]) (hp : p ≠ 0) :
    (run p).rightRoots = rightCount (denote p) ∧ (run p).axisRoots = axisCount (denote p) := by
  by_cases hn : p.natDegree=0
  · have he := eq_C_of_natDegree_eq_zero hn
    simp only [run, ite_eq_left hn]
    rw [he]
    simp [denote, rightCount, axisCount, regionCount]
  · obtain ⟨hc,hd,hq⟩ := ProofsG.input_spec p hp
    let s := (List.range p.natDegree).foldl (fun s j => ProofsG.step p.natDegree j s)
      (ProofsG.initial (ProofsG.input p) p.natDegree)
    have hi := ProofsG.loop_valid (ProofsG.rotated p) p.natDegree (ProofsG.input p)
      (by omega) hd hq hc p.natDegree le_rfl
    rw [Nat.sub_self] at hi
    have hf := FractionFree.ProofsFF.finish hi.1
    have hs := ProofsG.rotated_counts p
    have hout : s.2.2.2.2.1 = rightCount (denote p) ∧
        axisTotal s.2.2.2.2.2.1 s.2.2.2.2.1 = axisCount (denote p) :=
      ⟨hf.1.trans hs.1, hf.2.trans hs.2⟩
    simp only [run, ite_eq_right hn]
    simp only [← apply_ite (fun s : ProofsG.Locals (p.natDegree+1) =>
      (pure (ForInStep.yield s) : Id _)), List.forIn_pure_yield_eq_foldl]
    simpa only [s, ProofsG.step, ProofsG.initial, ProofsG.input, pure_bind, Id.run_pure] using hout

/-- Strict Hurwitz stability of the complex denotation is exactly acceptance. -/
theorem run_stable_iff (p : GaussianInt[X]) (hp : p ≠ 0) :
    (run p).stable = true ↔ ComplexStable (denote p) := by
  have hs := run_counts_correct p hp
  have he : (run p).stable = decide ((run p).rightRoots=0 ∧ (run p).axisRoots=0) := by
    by_cases hn : p.natDegree=0
    · simp [run,hn]
    · simp only [run, ite_eq_right hn]; rfl
  rw [he, decide_eq_true_eq, hs.1, hs.2, complexStable_iff_counts _ (denote_ne_zero p hp)]

end
end RouthHurwitz.ComplexRouth.Exact.Gaussian
