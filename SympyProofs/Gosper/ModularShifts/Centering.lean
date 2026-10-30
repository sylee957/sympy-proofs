module

public import SympyProofs.Gosper.ModularShifts.Algorithm

/-! Centering removes the coefficient that changes linearly under translation. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

theorem nextCoeff_taylor_monic {R : Type*} [CommRing R] (f : Polynomial R)
    (hf : f.Monic) (hd : 0 < f.natDegree) (s : R) :
    (taylor s f).nextCoeff = f.nextCoeff + (f.natDegree : R) * s := by
  rw [nextCoeff_of_natDegree_pos (by simpa using hd), natDegree_taylor, taylor_coeff]
  have hdeg : (hasseDeriv (f.natDegree - 1) f).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by omega)
  rw [eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff]
  have hn : 1 + (f.natDegree - 1) = f.natDegree := by omega
  simp only [hn, zero_add, Nat.choose_self, Nat.cast_one, one_mul, hf.coeff_natDegree,
    mul_one, nextCoeff_of_natDegree_pos hd]
  rw [Nat.choose_symm (by omega : 1 ≤ f.natDegree), Nat.choose_one_right]
  ring

theorem mean_taylor {m : ℕ} (f : Polynomial (ZMod m)) (hf : f.Monic)
    (hd : 0 < f.natDegree) (hu : IsUnit (f.natDegree : ZMod m)) (a : ZMod m) :
    mean (taylor a f) = mean f + a := by
  simp only [mean, natDegree_taylor, nextCoeff_taylor_monic f hf hd, add_mul]
  rw [mul_right_comm (f.natDegree : ZMod m) a, ZMod.mul_inv_of_unit _ hu, one_mul]

theorem center_taylor {m : ℕ} (f : Polynomial (ZMod m)) (hf : f.Monic)
    (hd : 0 < f.natDegree) (hu : IsUnit (f.natDegree : ZMod m)) (a : ZMod m) :
    center (taylor a f) = center f := by
  simp [center, mean_taylor f hf hd hu, taylor_taylor]

/-- With the convention `gcd(p(x), q(x+h))`, the sign is the coefficient of
`f` minus the coefficient of `g`, where `f = g(x+h)`. -/
theorem candidate_residue {m : ℕ} (g : Polynomial (ZMod m)) (hg : g.Monic)
    (hd : 0 < g.natDegree) (hu : IsUnit (g.natDegree : ZMod m)) (h : ZMod m) :
    ((taylor h g).nextCoeff - g.nextCoeff) * ((taylor h g).natDegree : ZMod m)⁻¹ = h := by
  rw [nextCoeff_taylor_monic g hg hd, add_sub_cancel_left, natDegree_taylor,
    mul_right_comm, ZMod.mul_inv_of_unit _ hu, one_mul]

theorem recover_integer {m : ℕ} (hm : 0 < m) (B : ℕ) (hB : 2 * B < m)
    (h : ℤ) (hh : |h| ≤ (B : ℤ)) : (h : ZMod m).valMinAbs = h := by
  let : NeZero m := ⟨by omega⟩
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_, ?_⟩ <;> obtain ⟨hl, hr⟩ := abs_le.mp hh <;> omega

end Gosper.ModularShifts
