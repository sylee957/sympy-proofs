module

public import SympyProofs.Calculus.Antiderivative.Proof.Verify.RootSum

/-! Exact verification differentiates each regular answer and permits checking the result by
equality in the executable fraction field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k]
variable {n : ℕ}

/-- The executable derivative of a regular answer exists and agrees with its model derivative. -/
theorem Answer.differentiateAlong_spec (ds : List (K R n)) (a : Answer R n) (h : a.Regular k) :
    ∃ x, a.differentiateAlong ds = some x ∧ val k x = a.derivAlong k ds := by
  have logs (ss : List (RootSum R n)) (hs : ∀ s ∈ ss, s.Regular k) :
      ∃ xs, ss.mapM (RootSum.differentiateAlong ds) = some xs ∧
        val k xs.sum = (ss.map (RootSum.derivAlong k ds)).sum := by
    induction ss with
    | nil => exact ⟨[],rfl,map_zero _⟩
    | cons s ss ih =>
      obtain ⟨x,hx,hv⟩ := s.differentiateAlong_spec k ds (hs s List.mem_cons_self)
      obtain ⟨xs,hxs,hvs⟩ := ih fun u hu => hs u (List.mem_cons_of_mem _ hu)
      exact ⟨x::xs,by simp [List.mapM_cons,hx,hxs], by simp [hv,hvs]⟩
  obtain ⟨xs,hxs,hv⟩ := logs a.sums h
  exact ⟨K.der ds a.field + xs.sum,by simp [differentiateAlong,hxs],
    by rw [derivAlong, map_add, val_der k ds, Model.derivation_apply, hv]⟩

/-- A regular answer passes the equality check exactly when its model derivative is the input. -/
theorem Answer.differentiateAlong_eq_some_iff (ds : List (K R n)) (a : Answer R n)
    (h : a.Regular k) (f : K R n) :
    a.differentiateAlong ds = some f ↔ a.derivAlong k ds = val k f := by
  obtain ⟨x, hx, hv⟩ := a.differentiateAlong_spec k ds h
  rw [hx, Option.some.injEq, ← hv]
  exact (val_injective k).eq_iff.symm

/-- Exact differentiation computes the model derivative of a regular answer in its tower. -/
theorem Answer.differentiate_spec (t : Tower R n) (a : Answer R n) (h : a.Regular k) :
    ∃ x, a.differentiate t = some x ∧ val k x = a.deriv k t :=
  a.differentiateAlong_spec k t.gens h

/-- Equality with the exact derivative verifies a regular answer in the original tower. -/
theorem Answer.differentiate_eq_some_iff (t : Tower R n) (a : Answer R n) (h : a.Regular k)
    (f : K R n) : a.differentiate t = some f ↔ a.deriv k t = val k f :=
  a.differentiateAlong_eq_some_iff k t.gens h f

/-- Every positive verdict satisfying the integrator specification verifies by exact arithmetic. -/
theorem Level.integrate_differentiate {t : Tower R n} {L : Level R n}
    (hL : L.IntegrateSpec k t)
    {f : K R n} {a : Answer R n} (h : L.integrate f = .elementary a) :
    a.differentiate t = some f := by
  have ha := hL f
  rw [h] at ha
  exact (a.differentiate_eq_some_iff k t ha.1 f).mpr ha.2

end SympyProofs.Calculus.Antiderivative
