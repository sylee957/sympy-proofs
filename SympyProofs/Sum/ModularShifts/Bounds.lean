module

public import SympyProofs.Sum.ModularShifts.Algorithm

/-! Rational Cauchy bounds for reconstructing a shift from its residue modulo a prime power. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

private theorem cauchyBound_le_radius (p : Polynomial ℚ) :
    ((p.map (algebraMap ℚ ℂ)).cauchyBound : ℝ) ≤ (radius p : ℝ) := by
  unfold Polynomial.cauchyBound radius
  simp only [natDegree_map, leadingCoeff_map, coeff_map, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_one, coe_nnnorm]
  push_cast
  change (((Finset.range p.natDegree).sup (fun i => ‖(p.coeff i : ℂ)‖₊) : NNReal) : ℝ) /
      ‖(p.leadingCoeff : ℂ)‖ + 1 ≤
    1 + (∑ i ∈ Finset.range p.natDegree, |(p.coeff i : ℝ)|) / |(p.leadingCoeff : ℝ)|
  rw [Complex.norm_ratCast, add_comm (1 : ℝ)]
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have hs : (Finset.range p.natDegree).sup (fun i => ‖(p.coeff i : ℂ)‖₊) ≤
      ∑ i ∈ Finset.range p.natDegree, ‖(p.coeff i : ℂ)‖₊ := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (f := fun i => ‖(p.coeff i : ℂ)‖₊) (fun _ _ => zero_le) hi
  simpa only [NNReal.coe_sum, coe_nnnorm, Complex.norm_ratCast] using
    (show (((Finset.range p.natDegree).sup (fun i => ‖(p.coeff i : ℂ)‖₊) : NNReal) : ℝ) ≤
      ((∑ i ∈ Finset.range p.natDegree, ‖(p.coeff i : ℂ)‖₊ : NNReal) : ℝ) from hs)

/-- A common complex root bounds the difference between two roots of the inputs. -/
theorem abs_shift_le_bound (p q : Polynomial ℚ) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ℤ) (hov : ¬IsCoprime p (taylor (h : ℚ) q)) :
    |h| ≤ (⌈radius p + radius q⌉₊ : ℤ) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ] at hov
  push Not at hov
  obtain ⟨z, hpz, hqz⟩ := hov
  have hpz' : (p.map (algebraMap ℚ ℂ)).IsRoot z := by
    simpa only [IsRoot.def, eval_map_algebraMap] using hpz
  have hqz' : (q.map (algebraMap ℚ ℂ)).IsRoot (z + (h : ℂ)) := by
    simpa [IsRoot.def, ← eval_map_algebraMap, map_taylor, taylor_eval] using hqz
  have hb1 := hpz'.norm_lt_cauchyBound (by simpa using hp)
  have hb2 := hqz'.norm_lt_cauchyBound (by simpa using hq)
  have hh : ‖(h : ℂ)‖ ≤ ‖z‖ + ‖z + (h : ℂ)‖ := by
    simpa [norm_sub_rev, add_comm] using norm_sub_le (z + (h : ℂ)) z
  have hlt : (|h| : ℝ) < ((radius p + radius q : ℚ) : ℝ) := by
    have hb1' : ‖z‖ < (radius p : ℝ) :=
      (show ‖z‖ < ((p.map (algebraMap ℚ ℂ)).cauchyBound : ℝ) from hb1).trans_le
        (cauchyBound_le_radius p)
    have hb2' : ‖z + (h : ℂ)‖ < (radius q : ℝ) :=
      (show ‖z + (h : ℂ)‖ < ((q.map (algebraMap ℚ ℂ)).cauchyBound : ℝ) from hb2).trans_le
        (cauchyBound_le_radius q)
    simpa using hh.trans_lt (add_lt_add hb1' hb2')
  have hceil : ((radius p + radius q : ℚ) : ℝ) ≤ (⌈radius p + radius q⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (radius p + radius q))
  exact_mod_cast (hlt.trans_le hceil).le

end Gosper.ModularShifts
