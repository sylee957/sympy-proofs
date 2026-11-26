module

public import SympyProofs.Calculus.Antiderivative.Program.Kind.Exp
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Coefficients

/-! The differential equations for every Laurent coefficient over the lower field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Exp

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable {t : Tower R n} {lower : Level R n} (hs : lower.SolveSpec k t)

include hs

/-- Each returned nonconstant coefficient solves its differential equation. The constant
coefficient is zero because the lower integrator treats that power separately. -/
theorem coefficients_sound {du : K R n} {s j : ℕ} {as bs : List (K R n)}
    (h : coefficients lower du s j as = some bs) :
    bs.length = as.length ∧ ∀ i : ℕ,
      if j+i = s then bs.getD i 0 = 0 else
        t.modelD k (val k (bs.getD i 0)) +
            (((j+i : ℕ) : M k n) - s) * val k du * val k (bs.getD i 0) = val k (as.getD i 0) := by
  induction as generalizing j bs with
  | nil =>
    obtain rfl : ([] : List (K R n)) = bs := Option.some.inj h
    simp
  | cons a as ih =>
    let sol := if j = s then some (0 : K R n) else lower.rde (((j : K R n) - s) * du) a
    have he : coefficients lower du s j (a :: as) = sol.bind (fun b =>
        (coefficients lower du s (j+1) as).bind (fun rs => some (b :: rs))) := by
      rw [coefficients]
      by_cases hj : j = s <;> simp [sol, hj]
    rw [he] at h
    cases hb : sol with
    | none => rw [hb] at h; cases h
    | some b =>
      cases hr : coefficients lower du s (j+1) as with
      | none => simp [hb, hr] at h
      | some rs =>
        obtain rfl : b :: rs = bs := by simpa [hb, hr] using h
        obtain ⟨hlen,hspec⟩ := ih hr
        refine ⟨by simp [hlen], ?_⟩
        intro i
        cases i with
        | zero =>
          by_cases hj : j = s
          · simpa [sol, hj, eq_comm] using hb
          · have h₀ : lower.rde (((j : K R n)-s)*du) a = some b := by simpa [sol, hj] using hb
            simpa [hj] using Level.rde_sound k hs h₀
        | succ i =>
          simpa only [List.getD_cons_succ, show j + (i+1) = j+1+i by omega] using hspec i

/-- The computation succeeds whenever all required equations have solutions over the model,
even when those solutions use constants outside the computational field. -/
theorem coefficients_complete (du : K R n) (s j : ℕ) (as : List (K R n))
    (h : ∀ i : ℕ, i < as.length → j+i ≠ s → ∃ y : M k n,
      t.modelD k y + (((j+i : ℕ) : M k n) - s) * val k du * y = val k (as.getD i 0)) :
    ∃ bs, coefficients lower du s j as = some bs := by
  induction as generalizing j with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    obtain ⟨rs,hr⟩ := ih (j+1) fun i hi hne => by
      simpa only [List.getD_cons_succ, show j + (i+1) = j+1+i by omega] using
        h (i+1) (by simpa using hi) (by omega)
    by_cases hj : j = s
    · subst j
      exact ⟨0 :: rs, by simp [coefficients, hr]⟩
    · cases hb : lower.rde (((j : K R n) - s) * du) a with
      | none =>
        apply False.elim ((Level.rde_complete k hs hb) ?_)
        simpa using h 0 (by simp) (by simpa using hj)
      | some b => exact ⟨b :: rs, by simp [coefficients, hj, hb, hr]⟩

end SympyProofs.Calculus.Antiderivative.Kind.Exp
