module

public import SympyProofs.Calculus.Antiderivative.Program.Tower

/-! The tower derivation agrees with the derivation below and differentiates the new generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

namespace K

/-- Partial differentiation in a lower generator commutes with adjoining a new variable. -/
theorem pderiv_lift (i : Fin n) (x : K R n) :
    pderiv i (lift x) = lift (pderiv i x) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    apply equiv.injective
    change equiv (pderiv i.castSucc (ofRaw (a.atHeight n))) = equiv (lift (pderiv i (ofRaw a)))
    rw [equiv_lift, pderiv_ofRaw, pderiv_ofRaw, equiv_ofRaw, equiv_ofRaw, value_pderiv i.castSucc,
      value_pderiv i]
    simp only [quotientRule, Raw.atHeight, MPoly.Raw.toMvPolynomial_atHeight (Nat.le_succ n),
      map_div₀, map_sub, map_mul, map_pow, Model.includeVars_polynomial]
    simp only [show Fin.castLE (Nat.le_succ n) = Fin.castSucc from rfl,
      MvPolynomial.pderiv_rename (Fin.castSucc_injective n)]

omit [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
private theorem pderiv_rename_last (p : MvPolynomial (Fin n) R) :
    MvPolynomial.pderiv (Fin.last n) (MvPolynomial.rename Fin.castSucc p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, MvPolynomial.pderiv_X_of_ne (Fin.castSucc_ne_last i)]

/-- Elements of the lower field are independent of the new variable. -/
theorem pderiv_last_lift (x : K R n) : pderiv n (lift x) = 0 := by
  induction x using Quotient.inductionOn with
  | _ a =>
    apply equiv.injective
    change equiv (pderiv (Fin.last n) (ofRaw (a.atHeight n))) = _
    rw [pderiv_ofRaw, equiv_ofRaw, value_pderiv (Fin.last n)]
    simp [Raw.atHeight, MPoly.Raw.toMvPolynomial_atHeight (Nat.le_succ n), quotientRule,
      show Fin.castLE (Nat.le_succ n) = Fin.castSucc from rfl, pderiv_rename_last]

private theorem weighted_lift (x : K R n) (v : K R (n + 1)) (ws : List (K R n)) (i : ℕ)
    (h : i + ws.length = n) :
    weightedPartials (lift x) i (ws.map lift ++ [v]) = lift (weightedPartials x i ws) := by
  induction ws generalizing i with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at h
    simp [h, weightedPartials_cons, weightedPartials, pderiv_last_lift]
  | cons u us ih =>
    have hi : i < n := by simp only [List.length_cons] at h; omega
    simp only [List.map_cons, List.cons_append, weightedPartials_cons, map_add, map_mul]
    rw [pderiv_lift (⟨i, hi⟩ : Fin n), ih (i + 1) (by simp_all [Nat.add_comm, Nat.add_assoc])]

/-- Appending a generator velocity to a complete list extends the previous derivation. -/
theorem der_lift (x : K R n) (ws : List (K R n)) (v : K R (n + 1)) (hw : ws.length = n) :
    der (ws.map lift ++ [v]) (lift x) = lift (der ws x) := by
  have hl : (ws.map lift ++ [v]).length = n + 1 := by simp [hw]
  rw [der_eq_weightedPartials, der_eq_weightedPartials, List.take_of_length_le hl.le,
    List.take_of_length_le hw.le]
  exact weighted_lift x v ws 0 (by simpa using hw)

private theorem weighted_gen (ws : List (K R (n + 1))) (v : K R (n + 1)) (i : ℕ)
    (h : i + ws.length = n) : weightedPartials gen i (ws ++ [v]) = v := by
  have hg : gen = ofPoly (MPoly.X (Fin.last n) : MPoly (n + 1) R) :=
    equiv.injective (by rw [equiv_gen, equiv_ofPoly, MPoly.equiv_X])
  induction ws generalizing i with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at h
    rw [List.nil_append, weightedPartials_cons, hg, pderiv_ofPoly_X]
    simp [h, weightedPartials]
  | cons u us ih =>
    have hi : i ≠ n := by simp only [List.length_cons] at h; omega
    rw [List.cons_append, weightedPartials_cons, ih (i + 1) (by
      simp only [List.length_cons] at h; omega), hg, pderiv_ofPoly_X]
    simp [hi]

/-- The last entry of a complete list is the derivative of the newest generator. -/
theorem der_gen (ws : List (K R (n + 1))) (v : K R (n + 1)) (hw : ws.length = n) :
    der (ws ++ [v]) gen = v := by
  have hl : (ws ++ [v]).length = n + 1 := by simp [hw]
  rw [der_eq_weightedPartials, List.take_of_length_le hl.le]
  exact weighted_gen ws v 0 (by simpa using hw)

end K

namespace ReducedGen

@[simp] theorem coe_prim {F : Type} (b : F) : ((prim b : ReducedGen F) : Gen F) = .prim b := rfl

@[simp] theorem coe_exp {F : Type} (u : F) : ((exp u : ReducedGen F) : Gen F) = .exp u := rfl

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
/-- Appending a primitive or exponential preserves the input certificate for the level solver. -/
theorem tangentFree_step (g : ReducedGen (K R n)) (t : Tower R n) (hf : t.TangentFree) :
    (t.step g).TangentFree := by cases g <;> exact hf

end ReducedGen

namespace Tower

omit [DecidableEq R] [NormalizedGCDMonoid R] [Div R] in
/-- Induct over the primitive and exponential steps of a certified tower. -/
@[elab_as_elim] theorem tangentFree_induct
    {P : {n : ℕ} → (t : Tower R n) → t.TangentFree → Prop}
    (base : P .base rfl)
    (step : ∀ {n} (t : Tower R n) (g : ReducedGen (K R n)) (hf : t.TangentFree),
      P t hf → P (t.step g) (g.tangentFree_step t hf)) :
    ∀ {n} (t : Tower R n) (hf : t.TangentFree), P t hf
  | _, .base, _ => base
  | _, .step t (.prim b), hf => step t (.prim b) hf (tangentFree_induct base step t hf)
  | _, .step t (.exp u), hf => step t (.exp u) hf (tangentFree_induct base step t hf)
  | _, .step _ (.tan _), hf => nomatch hf

@[simp] theorem length_gens (t : Tower R n) : t.gens.length = n := by
  induction t with
  | base => rfl
  | step t g ih => simp [gens, ih]

/-- Each tower step preserves the derivatives of the elements below it. -/
@[simp] theorem D_lift (t : Tower R n) (g : Gen (K R n)) (x : K R n) :
    (t.step g).D (K.lift x) = K.lift (t.D x) := K.der_lift x t.gens _ t.length_gens

/-- Adjoining a primitive gives it the prescribed derivative. -/
@[simp] theorem D_gen_prim (t : Tower R n) (b : K R n) :
    (t.step (.prim b)).D K.gen = K.lift b :=
  K.der_gen _ _ (by simp)

/-- The logarithmic derivative of a new exponential is the derivative of its exponent. -/
@[simp] theorem D_gen_exp (t : Tower R n) (u : K R n) :
    (t.step (.exp u)).D K.gen = K.lift (t.D u) * K.gen :=
  K.der_gen _ _ (by simp)

/-- The newest tangent generator satisfies its Riccati equation. -/
@[simp] theorem D_gen_tan (t : Tower R n) (u : K R n) :
    (t.step (.tan u)).D K.gen = K.lift (t.D u) * (1 + K.gen ^ 2) := K.der_gen _ _ (by simp)

end Tower

end SympyProofs.Calculus.Antiderivative
