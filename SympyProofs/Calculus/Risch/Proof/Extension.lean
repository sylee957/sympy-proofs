module

public import SympyProofs.Calculus.Risch.Spec.Extension
public import SympyProofs.Calculus.Risch.Proof.Integrate

/-! Completeness in the language of terms. The field of a tower obtained from `t` by
adjoining exponentials and logarithms is an elementary extension of the field of `t` when
the larger tower is admissible. So when `integrate` finds no elementary integral, no answer
written in such a tower, a term together with sums of logarithms over roots, has the
integrand as its derivative. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Differential LiouvilleForm

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

variable (k) in
/-- The inclusion of the field of depth `n` in the field of depth `n + d`. -/
noncomputable def liftHom (n : ℕ) : (d : ℕ) → K k n →+* K k (n + d)
  | 0 => RingHom.id _
  | d + 1 => (RatFunc.C : K k (n + d) →+* RatFunc (K k (n + d))).comp (liftHom n d)

/-- A lifted term denotes the image of its value. -/
theorem Term.value_lift : ∀ (d : ℕ) (e : Term n),
    Term.value k (e.lift d) = liftHom k n d (Term.value k e)
  | 0, _ => rfl
  | d + 1, e => by
    rw [Term.lift, Term.value_weaken, Term.value_lift d e]
    rfl

theorem liftHom_constHom : ∀ (d : ℕ) (c : k),
    liftHom k n d (constHom k n c) = constHom k (n + d) c
  | 0, _ => rfl
  | d + 1, c => by
    change RatFunc.C (liftHom k n d (constHom k n c)) = RatFunc.C (constHom k (n + d) c)
    rw [liftHom_constHom d c]

/-- The field of an admissible tower obtained by adjoining exponentials and logarithms is an
elementary extension of the field it starts from, with the same derivation below. -/
theorem Tower.ElementaryExt.tower {t : Tower n} {d : ℕ} {t' : Tower (n + d)}
    (ext : t.ElementaryExt d t') (ht' : t'.Admissible k) :
    letI : Differential (K k n) := ⟨t.der k⟩
    letI : Differential (K k (n + d)) := ⟨t'.der k⟩
    letI : Algebra (K k n) (K k (n + d)) := (liftHom k n d).toAlgebra
    DifferentialAlgebra (K k n) (K k (n + d)) ∧ ElementaryTower (K k n) (K k (n + d)) := by
  induction ext with
  | refl =>
    let : Differential (K k n) := ⟨t.der k⟩
    exact ⟨⟨fun _ => rfl⟩, ElementaryTower.base⟩
  | @exp d s _ u ih =>
    obtain ⟨hs, -, -⟩ := ht'
    obtain ⟨da, tw⟩ := ih hs
    let : Differential (K k n) := ⟨t.der k⟩
    let : Differential (K k (n + d)) := ⟨s.der k⟩
    let : Differential (RatFunc (K k (n + d))) := ⟨(s.exp u).der k⟩
    let : Algebra (K k n) (K k (n + d)) := (liftHom k n d).toAlgebra
    let : Algebra (K k n) (RatFunc (K k (n + d))) := (liftHom k n (d + 1)).toAlgebra
    have := IsScalarTower.of_algebraMap_eq (R := K k n) (S := K k (n + d))
      (A := RatFunc (K k (n + d))) fun _ => rfl
    have : DifferentialAlgebra (K k n) (K k (n + d)) := da
    have : DifferentialAlgebra (K k (n + d)) (RatFunc (K k (n + d))) :=
      ⟨fun a => by rw [RatFunc.algebraMap_eq_C]; exact s.der_exp_C u a⟩
    have : ContainConstants (K k n) (K k (n + d)) := ⟨fun {x} hx => by
      obtain ⟨c, rfl⟩ := (s.der_eq_zero_iff hs x).mp hx
      exact ⟨constHom k n c, liftHom_constHom d c⟩⟩
    change DifferentialAlgebra (K k n) (RatFunc (K k (n + d))) ∧
      ElementaryTower (K k n) (RatFunc (K k (n + d)))
    refine ⟨⟨fun a => ?_⟩, ElementaryTower.adjoin tw
      (.exp AlgEquiv.refl (Term.value k u) ?_)⟩
    · change (s.exp u).der k (RatFunc.C (liftHom k n d a)) =
        RatFunc.C (liftHom k n d (t.der k a))
      rw [Tower.der_exp_C]
      exact congrArg RatFunc.C (da.deriv_algebraMap a)
    · rw [RatFunc.algebraMap_eq_C]
      exact s.der_exp_X u
  | @log d s _ u ih =>
    have ht'' : (s.prim (.div (s.D u) u)).Admissible k := ht'
    obtain ⟨hs, -, np⟩ := ht''
    obtain ⟨da, tw⟩ := ih hs
    let : Differential (K k n) := ⟨t.der k⟩
    let : Differential (K k (n + d)) := ⟨s.der k⟩
    let : Differential (RatFunc (K k (n + d))) := ⟨(s.prim (.div (s.D u) u)).der k⟩
    let : Algebra (K k n) (K k (n + d)) := (liftHom k n d).toAlgebra
    let : Algebra (K k n) (RatFunc (K k (n + d))) := (liftHom k n (d + 1)).toAlgebra
    have := IsScalarTower.of_algebraMap_eq (R := K k n) (S := K k (n + d))
      (A := RatFunc (K k (n + d))) fun _ => rfl
    have : DifferentialAlgebra (K k n) (K k (n + d)) := da
    have : DifferentialAlgebra (K k (n + d)) (RatFunc (K k (n + d))) :=
      ⟨fun a => by rw [RatFunc.algebraMap_eq_C]; exact s.der_prim_C _ a⟩
    have : ContainConstants (K k n) (K k (n + d)) := ⟨fun {x} hx => by
      obtain ⟨c, rfl⟩ := (s.der_eq_zero_iff hs x).mp hx
      exact ⟨constHom k n c, liftHom_constHom d c⟩⟩
    have val : Term.value k (.div (s.D u) u) = logDeriv (Term.value k u) := by
      change Term.value k (s.D u) / Term.value k u = _
      rw [← Tower.der_value]
      rfl
    change DifferentialAlgebra (K k n) (RatFunc (K k (n + d))) ∧
      ElementaryTower (K k n) (RatFunc (K k (n + d)))
    refine ⟨⟨fun a => ?_⟩, ElementaryTower.adjoin tw
      (.log AlgEquiv.refl (Term.value k u) (fun ⟨w, hw⟩ => np ⟨w, hw.trans val.symm⟩) ?_)⟩
    · change (s.prim (.div (s.D u) u)).der k (RatFunc.C (liftHom k n d a)) =
        RatFunc.C (liftHom k n d (t.der k a))
      rw [Tower.der_prim_C]
      exact congrArg RatFunc.C (da.deriv_algebraMap a)
    · rw [RatFunc.algebraMap_eq_C, ← val]
      exact s.der_prim_X _

/-- A tower accepted by `admissible` stays accepted without its last generators. -/
theorem Tower.ElementaryExt.admissible_base {t : Tower n} {d : ℕ} {t' : Tower (n + d)}
    (ext : t.ElementaryExt d t') (h : admissible t' = true) : admissible t = true := by
  induction ext with
  | refl => exact h
  | exp _ u ih =>
    simp only [admissible, Bool.and_eq_true] at h
    exact ih h.1.1
  | log _ u ih =>
    simp only [Tower.log, admissible, Bool.and_eq_true] at h
    exact ih h.1.1.1

variable [IsAlgClosed k] {t : Tower n} {f : Term n}

/-- **Completeness in the language of terms.** When `integrate` returns `nonelementary`, no
answer written in a tower obtained from `t` by adjoining exponentials and logarithms has the
integrand as its derivative, provided the larger tower is accepted by `admissible`. An
answer is a term together with sums of logarithms over the roots of polynomials. -/
theorem integrate_no_answer (hf : f.defined = true) (h : integrate t f = .nonelementary)
    {d : ℕ} {t' : Tower (n + d)} (ext : t.ElementaryExt d t') (ht' : admissible t' = true)
    (a : Answer (n + d)) : a.deriv k t' ≠ Term.value k (f.lift d) := by
  intro eq
  have ht := ext.admissible_base ht'
  have adm' : t'.Admissible k := admissible_sound ht'
  let : Differential (K k n) := ⟨t.der k⟩
  let : Differential (K k (n + d)) := ⟨t'.der k⟩
  let : Algebra (K k n) (K k (n + d)) := (liftHom k n d).toAlgebra
  obtain ⟨da, tw⟩ := ext.tower adm'
  have : DifferentialAlgebra (K k n) (K k (n + d)) := da
  have : IsLiouville (K k n) (K k (n + d)) := tw.isLiouville
  have e1 : t'.Elementary k (algebraMap (K k n) (K k (n + d)) (Term.value k f)) := by
    have := Answer.deriv_elementary (k := k) t' a
    rwa [eq, Term.value_lift] at this
  have e2 := (t'.elementary_iff_form adm' _).mp e1
  have e3 := (form_iff_of_constants (K := K k n) (fun v hv => by
    obtain ⟨c, rfl⟩ := (t'.der_eq_zero_iff adm' v).mp hv
    exact ⟨constHom k n c, liftHom_constHom d c⟩) _).mp e2
  have e4 := (form_in_extension_iff (K k (n + d)) (Term.value k f)).mp e3
  exact integrate_complete ht hf h ((t.elementary_iff_form (admissible_sound ht) _).mpr e4)

/-- When `integrate` returns `nonelementary`, no term of a tower obtained from `t` by
adjoining exponentials and logarithms has the integrand as its derivative, provided the
larger tower is accepted by `admissible`. -/
theorem integrate_no_term (hf : f.defined = true) (h : integrate t f = .nonelementary)
    {d : ℕ} {t' : Tower (n + d)} (ext : t.ElementaryExt d t') (ht' : admissible t' = true)
    (g : Term (n + d)) : Term.value k (t'.D g) ≠ Term.value k (f.lift d) := by
  have := integrate_no_answer (k := k) hf h ext ht' ⟨g, []⟩
  rwa [Answer.deriv, List.map_nil, List.sum_nil, add_zero, Tower.der_value] at this

end SympyProofs.Calculus.Risch
