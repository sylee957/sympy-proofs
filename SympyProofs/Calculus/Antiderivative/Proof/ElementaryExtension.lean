module

public import SympyProofs.Calculus.Antiderivative.Proof.Liouville
public import SympyProofs.Calculus.Antiderivative.Proof.ConstantsConverse
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Add

/-! Adjoining logarithms and exponentials to an admissible tower preserves the elementary
integrability of elements of its input field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n m : ℕ}

/-- A larger tower written by adjoining finitely many exponentials and logarithms. -/
inductive Tower.ElementaryExt (t : Tower R n) : {m : ℕ} → Tower R m → Prop where
  | refl : t.ElementaryExt t
  | exp {j : ℕ} {v : Tower R j} (lower : t.ElementaryExt v) (u : K R j) :
    t.ElementaryExt (v.step (.exp u))
  | log {j : ℕ} {v : Tower R j} (lower : t.ElementaryExt v) (u : K R j) :
    t.ElementaryExt (v.step (.prim (v.D u / u)))

theorem Tower.ElementaryExt.height {t : Tower R n} {t' : Tower R m}
    (h : t.ElementaryExt t') :
    n ≤ m := by
  induction h with
  | refl => rfl
  | exp _ _ ih | log _ _ ih => exact ih.trans (Nat.le_succ _)

variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

omit [CharZero k] in
theorem Model.includeVars_trans {j : ℕ} (h : n ≤ m) (h' : m ≤ j) (x : M k n) :
    Model.includeVars h' (Model.includeVars h x) = Model.includeVars (h.trans h') x := by
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) k) x
  simp only [map_div₀, Model.includeVars_polynomial, MvPolynomial.rename_rename]
  rfl

omit [CharZero k] in
theorem Model.includeVars_refl (x : M k n) : Model.includeVars le_rfl x = x := by
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) k) x
  simp only [map_div₀, Model.includeVars_polynomial]
  simp

private theorem log_descend {t : Tower R n} (ht : t.Admissible k) (u : K R n)
    (hu : (ReducedGen.prim (t.D u / u)).Admissible k t) {x : M k n}
    (h : (t.step (.prim (t.D u/u))).Elementary k (Model.includeVars (Nat.le_succ n) x)) :
    t.Elementary k x := by
  let b := t.D u / u
  have liftC : (Model.stepEquiv k n).symm (algebraMap _ _ (C x)) =
      Model.includeVars (Nat.le_succ n) x := by
    apply (Model.stepEquiv k n).injective
    simp [Model.stepEquiv_includeVars]
  obtain ⟨p,hd,hlo,hD⟩ := (t.elementary_prim_polynomial_iff k b ht hu (C x)).mp (liftC ▸ h)
  have hd' : p.natDegree ≤ 1 := by simpa using hd
  have hzero : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : t.modelD k (p.coeff 1) = 0 := by simpa [hzero] using hD 0 (Nat.zero_le _)
  obtain ⟨c,hc⟩ := (ht _).mp h1
  have hlog : t.Elementary k (val k b * p.coeff 1) := by
    refine ⟨0,[(c,val k u)],?_⟩
    simp [b,hc,mul_comm]
  rw [coeff_C_zero] at hlo
  simpa only [sub_add_cancel] using hlo.add k hlog

/-- Every elementary answer over a larger explicit tower descends to an elementary form over
the input tower, when its derivative belongs to the input field. -/
theorem Tower.ElementaryExt.descend {t : Tower R n} {t' : Tower R m}
    (e : t.ElementaryExt t')
    (ht' : t'.Admissible k) (x : M k n) (h : t'.Elementary k (Model.includeVars e.height x)) :
    t.Elementary k x := by
  induction e with
  | refl => simpa only [Model.includeVars_refl] using h
  | @exp j v lower u ih =>
    have lowerAdm := ((v.admissible_step_iff k (.exp u)).mp ht').1
    apply ih lowerAdm
    let y := Model.includeVars lower.height x
    have he : (Model.stepEquiv k j).symm (algebraMap _ _ (C y) / RatFunc.X ^ 0) =
        Model.includeVars (Nat.le_succ j) y := by
      apply (Model.stepEquiv k j).injective
      simp [Model.stepEquiv_includeVars]
    have hy := (v.elementary_exp_laurent_necessary k u lowerAdm (C y) 0
      (by rw [he,Model.includeVars_trans]; exact h)).1
    simpa only [coeff_C_zero] using hy
  | @log j v lower u ih =>
    obtain ⟨lowerAdm, genAdm⟩ := (v.admissible_step_iff k (.prim (v.D u / u))).mp ht'
    apply ih lowerAdm
    exact log_descend k lowerAdm u genAdm (by rw [Model.includeVars_trans]; exact h)

end SympyProofs.Calculus.Antiderivative
