module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import SympyProofs.LinearAlgebra.MatrixExponential.Basic

/-!
# Exponential and logarithm on nilpotent elements

The formal logarithm becomes a finite expression at a nilpotent element.
This is the algebraic ingredient for the principal logarithm on generalized
eigenspaces, where diagonalizability is not available.
-/

@[expose] public section

namespace SympyProofs.MatrixExponential.Nilpotent

namespace Formal

open PowerSeries

variable {R : Type*} [CommRing R]

noncomputable def eval (a : R) (f : PowerSeries R) : R :=
  MvPowerSeries.constantCoeff (f.subst (C a))

private theorem hasSubst_C {a : R} (ha : IsNilpotent a) :
    HasSubst (C a : PowerSeries R) := by
  change IsNilpotent (PowerSeries.constantCoeff (C a))
  simpa using ha

theorem eval_eq_finsum {a : R} (ha : IsNilpotent a) (f : PowerSeries R) :
    eval a f = ∑ᶠ k : ℕ, coeff k f * a ^ k := by
  rw [eval, constantCoeff_subst (hasSubst_C ha)]
  simp only [map_pow, C_apply, MvPowerSeries.constantCoeff_C, smul_eq_mul]

theorem subst_C_eq {a : R} (ha : IsNilpotent a) (f : PowerSeries R) :
    f.subst (C a : PowerSeries R) = C (eval a f) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp [eval, constantCoeff_eq]
  · rw [coeff_subst' (hasSubst_C ha), coeff_C, ite_eq_right hk]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    simp only [← map_pow, coeff_C, ite_eq_right hk, smul_zero]

theorem eval_subst {a : R} (ha : IsNilpotent a)
    {g : PowerSeries R} (hg : HasSubst g) (f : PowerSeries R) :
    eval a (f.subst g) = eval (eval a g) f := by
  simp only [eval]
  rw [subst_comp_subst_apply hg (hasSubst_C ha), subst_C_eq ha g]
  simp only [C_apply, MvPowerSeries.constantCoeff_C]

theorem eval_nilpotent {a : R} (ha : IsNilpotent a)
    {f : PowerSeries R} (hf : HasSubst f) : IsNilpotent (eval a f) := by
  simpa only [HasSubst, coe_substAlgHom, eval] using hf.comp (hasSubst_C ha)

@[simp] theorem eval_X {a : R} (ha : IsNilpotent a) : eval a X = a := by
  rw [eval, subst_X (hasSubst_C ha)]
  exact constantCoeff_C a

theorem eval_eq_sum {a : R} {m : ℕ} (hm : a ^ m = 0) (f : PowerSeries R) :
    eval a f = ∑ k ∈ Finset.range m, coeff k f * a ^ k := by
  rw [eval_eq_finsum ⟨m, hm⟩]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra hkm
  have hmk : m ≤ k := by simpa using hkm
  exact hk (by simp [pow_eq_zero_of_le hmk hm])

variable [Algebra ℚ R]

/-- The finite logarithm of `1 + a` when `a` is nilpotent. -/
noncomputable def log (a : R) : R := eval a (PowerSeries.log R)

theorem isNilpotent_log {a : R} (ha : IsNilpotent a) : IsNilpotent (log a) :=
  eval_nilpotent ha HasSubst.log

theorem eval_exp {a : R} (ha : IsNilpotent a) :
    eval a (PowerSeries.exp R) = IsNilpotent.exp a := by
  obtain ⟨m, hm⟩ := ha
  rw [eval_eq_sum hm, IsNilpotent.exp_eq_sum hm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [coeff_exp, Algebra.smul_def, one_div]

theorem exp_log {a : R} (ha : IsNilpotent a) :
    IsNilpotent.exp (log a) = 1 + a := by
  rw [← eval_exp (isNilpotent_log ha), log, ← eval_subst ha HasSubst.log,
    PowerSeries.subst_exp_log]
  simp only [eval, ← coe_substAlgHom (hasSubst_C ha), map_add, map_one, substAlgHom_X]
  exact congrArg (1 + ·) (constantCoeff_C a)

theorem log_exp_sub_one {a : R} (ha : IsNilpotent a) :
    log (IsNilpotent.exp a - 1) = a := by
  have h : eval a (PowerSeries.exp R - 1) = IsNilpotent.exp a - 1 := by
    simp [eval, ← coe_substAlgHom (hasSubst_C ha), ← eval_exp ha]
  rw [log, ← h, ← eval_subst ha HasSubst.exp_sub_one, PowerSeries.subst_log_exp_sub_one]
  exact eval_X ha

end Formal

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

/-- The finite logarithm of `1 + a`. Its inverse laws require `a` to be nilpotent. -/
noncomputable def log (a : A) : A :=
  ∑ k ∈ Finset.range (nilpotencyClass a), ((-1 : ℚ) ^ (k + 1) / k) • a ^ k

theorem log_eq_sum {a : A} {m : ℕ} (hm : a ^ m = 0) :
    log a = ∑ k ∈ Finset.range m, ((-1 : ℚ) ^ (k + 1) / k) • a ^ k := by
  apply Finset.sum_subset (Finset.range_mono (show nilpotencyClass a ≤ m from csInf_le' hm))
  intro k hkm hkn
  rw [pow_eq_zero_of_le (by simpa using hkn) (pow_nilpotencyClass ⟨m, hm⟩), smul_zero]

theorem map_log {F : Type*} [FunLike F A B] [RingHomClass F A B]
    {a : A} (ha : IsNilpotent a) (f : F) :
    f (log a) = log (f a) := by
  obtain ⟨m, hm⟩ := ha
  have hm' : (f a) ^ m = 0 := by simp [← map_pow, hm]
  simp [log_eq_sum hm, log_eq_sum hm', map_rat_smul]

theorem isNilpotent_log {a : A} (ha : IsNilpotent a) : IsNilpotent (log a) := by
  apply Commute.isNilpotent_sum
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · exact (ha.pow_of_pos hk0).smul _
  · intro i j hi hj
    exact ((Commute.refl a).pow_pow i j).smul_left _ |>.smul_right _

private theorem formal_log_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    {a : R} (ha : IsNilpotent a) : Formal.log a = log a := by
  rw [Formal.log, Formal.eval_eq_sum (pow_nilpotencyClass ha), log]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [PowerSeries.coeff_log]
  · simp [PowerSeries.coeff_log, hk0, Algebra.smul_def]

theorem exp_log {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (log a) = 1 + a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := Formal.exp_log hx
  rw [formal_log_eq hx] at h
  have h' := congrArg S.val h
  rw [IsNilpotent.map_exp (isNilpotent_log hx), map_log hx, map_add, map_one] at h'
  exact h'

theorem log_exp_sub_one {a : A} (ha : IsNilpotent a) :
    log (IsNilpotent.exp a - 1) = a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := Formal.log_exp_sub_one hx
  rw [formal_log_eq hx.isNilpotent_exp_sub_one] at h
  have h' := congrArg S.val h
  rw [map_log hx.isNilpotent_exp_sub_one, map_sub, IsNilpotent.map_exp hx, map_one] at h'
  exact h'

theorem normedSpace_exp_eq [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    {a : A} (ha : IsNilpotent a) : NormedSpace.exp a = IsNilpotent.exp a := by
  rw [NormedSpace.exp_eq_tsum_rat, IsNilpotent.exp]
  apply tsum_eq_sum
  intro k hk
  rw [pow_eq_zero_of_le (by simpa using hk) (pow_nilpotencyClass ha), smul_zero]

end SympyProofs.MatrixExponential.Nilpotent
