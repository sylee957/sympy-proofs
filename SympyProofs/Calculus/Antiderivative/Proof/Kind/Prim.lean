module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Prim
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Coefficients
public import SympyProofs.Calculus.Antiderivative.Proof.TowerConstants

/-! The triangular equations at positive powers of a primitive generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Prim

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable {t : Tower R n} {lower : Level R n} (hs : lower.SolveSpec k t)

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

omit [CharZero k] in
private theorem derivative_correction (c : K R 0) (j : ℕ) :
    t.modelD k (val k (K.ofConst c / (j : K R n))) = 0 := by
  rw [map_div₀, map_natCast, ← Model.C_constantHom, Derivation.leibniz_div]
  simp

include hs

/-- The returned coefficients satisfy all the requested coefficient equations. -/
theorem coefficients_sound {b : K R n} {i : ℕ} {as : List (K R n)}
    {v : K R n} {ps : List (K R n)} (h : coefficients lower b i as = some (v,ps)) :
    ps.length = as.length ∧ ∀ j : ℕ,
      t.modelD k (val k ((v :: ps).getD j 0)) +
        ((i+j+1 : ℕ) : M k n) * val k b * val k ((v :: ps).getD (j+1) 0) =
          val k (as.getD j 0) := by
  induction as generalizing i v ps with
  | nil =>
    obtain ⟨rfl, rfl⟩ : (0 : K R n) = v ∧ ([] : List (K R n)) = ps :=
      Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, fun j => ?_⟩
    cases j <;> simp
  | cons a as ih =>
    cases ht : coefficients lower b (i+1) as with
    | none => simp [coefficients, ht] at h
    | some p =>
      rcases p with ⟨u, fixed⟩
      let m : K R n := (i+1 : ℕ)
      cases hc : lower.limited (a - m*b*u) b with
      | none => simp [coefficients, ht] at h; simp [m] at hc; simp [hc] at h
      | some p =>
        rcases p with ⟨c, w⟩
        change lower.limited (a - ((i+1 : ℕ) : K R n)*b*u) b = some (c,w) at hc
        rw [coefficients, ht] at h
        change (lower.limited (a - ((i+1 : ℕ) : K R n)*b*u) b).bind _ = _ at h
        rw [hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hl, he⟩ := ih ht
        refine ⟨by simp [hl], ?_⟩
        intro j
        cases j with
        | zero =>
          have hw := Level.limited_sound k hs hc
          simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, map_add, map_div₀,
            map_natCast, map_mul, map_sub] at hw ⊢
          rw [hw]
          have hn : ((i+1 : ℕ) : M k n) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp
          ring
        | succ j =>
          have eqn := he j
          rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
          have hn : i + (j+1) + 1 = i+1+j+1 := by omega
          rw [hn]
          cases j with
          | zero =>
            simpa only [List.getD_cons_zero, map_add, derivative_correction,
              add_zero, List.getD_cons_succ] using eqn
          | succ l => exact eqn

omit hs [CharZero k] in
private theorem no_scaled_primitive {b : K R n} (ha : (ReducedGen.prim b).Admissible k t)
    (c : k) (v : M k n) (h : t.modelD k v = Model.C k n c * val k b) : c = 0 := by
  by_contra hc
  apply ha
  refine ⟨v / Model.C k n c, ?_⟩
  rw [Derivation.leibniz_div_const _ _ _ (Tower.modelD_C k t c), smul_eq_mul, h]
  field_simp [(map_ne_zero (Model.C k n)).mpr hc]

/-- Every model solution of the finite triangular system gives a computed solution.
Its lowest coefficient agrees with the prescribed one up to a constant of the model. -/
theorem coefficients_complete {b : K R n} (ht : t.Admissible k)
    (hb : (ReducedGen.prim b).Admissible k t) (i : ℕ) (as : List (K R n)) (w : ℕ → M k n)
    (hbound : ∀ j, as.length < j → w j = 0)
    (he : ∀ j, t.modelD k (w j) +
      ((i+j+1 : ℕ) : M k n) * val k b * w (j+1) = val k (as.getD j 0)) :
    ∃ v ps c, coefficients lower b i as = some (v,ps) ∧ val k v - w 0 = Model.C k n c := by
  induction as generalizing i w with
  | nil =>
    have hw : t.modelD k (w 0) = 0 := by simpa [hbound 1 (by simp)] using he 0
    obtain ⟨c, hc⟩ := (ht _).mp hw
    exact ⟨0, [], -c, rfl, by simp [hc]⟩
  | cons a as ih =>
    obtain ⟨u, fixed, c, hrec, hu⟩ := ih (i+1) (fun j => w (j+1))
      (fun j hj => hbound _ (by simpa using hj))
      (fun j => by simpa only [List.getD_cons_succ, show i+(j+1)+1 = i+1+j+1 by omega]
                   using he (j+1))
    let m : K R n := (i+1 : ℕ)
    have hw : t.modelD k (w 0) + ((i+1 : ℕ) : M k n)*val k b*w 1 = val k a := by
      simpa using he 0
    have hi : val k m = ((i+1 : ℕ) : M k n) := map_natCast _ _
    have hk : Model.C k n ((i+1 : ℕ) : k) = val k m := (map_natCast _ _).trans hi.symm
    have hz : t.modelD k (w 0) =
        val k (a - m*b*u) - Model.C k n (-((i+1 : ℕ) : k) * c) * val k b := by
      rw [map_sub, map_mul, map_mul, map_mul, map_neg, hk, ← hu, hi]
      linear_combination hw
    cases hd : lower.limited (a - m*b*u) b with
    | none => exact False.elim ((Level.limited_complete k hs hd) ⟨_, w 0, hz⟩)
    | some p =>
      rcases p with ⟨c',v⟩
      have hv := Level.limited_sound k hs hd
      let d := -((i+1 : ℕ) : k) * c - Model.constantHom k c'
      have heq : t.modelD k (val k v - w 0) = Model.C k n d * val k b := by
        rw [map_sub, hv, hz, map_mul, ← Model.C_constantHom]
        simp only [d, map_sub]
        ring
      have hd0 := no_scaled_primitive k hb d (val k v - w 0) heq
      rw [hd0, map_zero, zero_mul] at heq
      obtain ⟨q,hq⟩ := (ht _).mp heq
      exact ⟨v, (u + K.ofConst c' / m) :: fixed, q,
        by rw [coefficients, hrec]; change (lower.limited (a - m*b*u) b).bind _ = _;
           rw [hd]; rfl, hq⟩

end SympyProofs.Calculus.Antiderivative.Kind.Prim
