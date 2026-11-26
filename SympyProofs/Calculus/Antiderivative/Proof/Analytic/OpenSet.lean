module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.Specialization

/-! Fraction specialization on open sets of a complex solution. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Filter Topology

variable {R : Type} [CommRing R] [IsDomain R] {n : ℕ}

/-- Exponentials are nonzero and tangents omit the two stationary values of their
Riccati equation. -/
def Tower.Nondegenerate : {m : ℕ} → Tower R m → (Fin m → ℂ) → Prop
  | _, .base, _ => True
  | _, .step t (.prim _), p => t.Nondegenerate (p ∘ Fin.castSucc)
  | m+1, .step t (.exp _), p => t.Nondegenerate (p ∘ Fin.castSucc) ∧ p (Fin.last m) ≠ 0
  | m+1, .step t (.tan _), p => t.Nondegenerate (p ∘ Fin.castSucc) ∧
    p (Fin.last m) ≠ Complex.I ∧ p (Fin.last m) ≠ -Complex.I

/-- Restricting a nondegenerate point to the lower generators preserves nondegeneracy. -/
theorem Tower.Nondegenerate.lower {t : Tower R n} {g : Gen (K R n)}
    {p : Fin (n+1) → ℂ}
    (h : (t.step g).Nondegenerate p) : t.Nondegenerate (p ∘ Fin.castSucc) := by
  cases g with
  | prim _ => exact h
  | exp _ => exact h.1
  | tan _ => exact h.1

variable [DecidableEq R] [NormalizedGCDMonoid R] [Div R] [Algebra R ℂ] [FaithfulSMul R ℂ]

/-- Restrict a tuple of generator functions to the tower below its newest generator. -/
def Model.lower (G : ℂ → Fin (n+1) → ℂ) : ℂ → Fin n → ℂ := fun z => G z ∘ Fin.castSucc

/-- A solution of the tower equations is a solution at each preceding height. -/
theorem Tower.SolvedBy.lower {t : Tower R n} {g : Gen (K R n)}
    {G : ℂ → Fin (n+1) → ℂ}
    {z : ℂ} (h : (t.step g).SolvedBy G z) : t.SolvedBy (Model.lower G) z := by
  intro i
  have he : ((t.step g).gens.map (val ℂ)).getD i.castSucc.val 0 =
      Model.includeVars (Nat.le_succ n) ((t.gens.map (val ℂ)).getD i.val 0) := by
    cases g <;> simp [Tower.gens, List.getD, i.isLt]
  obtain ⟨hr,hd⟩ := h i.castSucc
  rw [he] at hr hd
  have hv := Model.hasValue_include_iff.mp hr.hasValue
  exact ⟨⟨_,hv⟩, hv.evalAt.symm ▸ hd⟩

namespace Model

variable {G : ℂ → Fin n → ℂ} {V : Set ℂ} {v : List (M ℂ n)}

/-- The coordinates on an open set satisfy no polynomial identity over the complex numbers. -/
def IndependentOn (G : ℂ → Fin n → ℂ) (V : Set ℂ) : Prop :=
  ∀ p : MvPolynomial (Fin n) ℂ, (∀ z ∈ V, MvPolynomial.eval (G z) p = 0) → p = 0

/-- If the coordinates satisfy no polynomial identity, every rational identity holds formally. -/
theorem IndependentOn.eq_zero (h : IndependentOn G V) {x : M ℂ n}
    (hx : ∀ z ∈ V, HasValue (G z) x 0) : x = 0 := by
  obtain ⟨a,b,hb,hr⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) ℂ) x
  have hbn : polynomial ℂ b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  change polynomial ℂ a / polynomial ℂ b = x at hr
  have e := (eq_div_iff hbn).mp hr.symm
  have ha := h a fun z hz => by simpa using (hx z hz).eval_fraction e.symm
  simp [← hr, ha, polynomial]

/-- Nonzero fractions are regular and nonzero throughout a smaller nonempty open set. -/
theorem IndependentOn.exists_regular {x : M ℂ n} (hx : x ≠ 0) (h : IndependentOn G V)
    (openV : IsOpen V) (sol : ∀ z ∈ V, SolvedBy v G z) :
    ∃ W : Set ℂ, IsOpen W ∧ W.Nonempty ∧ W ⊆ V ∧
      ∀ z ∈ W, RegularAt (G z) x ∧ evalAt (G z) x ≠ 0 := by
  obtain ⟨a,b,hb,hr⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) ℂ) x
  have hbn : polynomial ℂ b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  change polynomial ℂ a / polynomial ℂ b = x at hr
  have ha : a ≠ 0 := fun e => hx (by simp [← hr, e, polynomial])
  have hprod : a*b ≠ 0 := mul_ne_zero ha (nonZeroDivisors.ne_zero hb)
  obtain ⟨w,hw,hn⟩ : ∃ z ∈ V, MvPolynomial.eval (G z) (a*b) ≠ 0 := by
    by_contra! e
    exact hprod (h _ e)
  have hp := HasValue.polynomial (p := G w) (a*b)
  obtain ⟨_,hd⟩ := hasDerivAt_evalAt (sol w hw) (show RegularAt _ _ from ⟨_,hp⟩)
  have hcont : ContinuousAt (fun z => MvPolynomial.eval (G z) (a*b)) w := by
    simpa only [HasValue.evalAt (HasValue.polynomial _)] using hd.continuousAt
  obtain ⟨W,sub,op,hw'⟩ := mem_nhds_iff.mp
    (show {z | z ∈ V ∧ MvPolynomial.eval (G z) (a*b) ≠ 0} ∈ 𝓝 w from
      (openV.eventually_mem hw).and (hcont.eventually_ne hn))
  refine ⟨W,op,⟨w,hw'⟩,fun z hz => (sub hz).1,fun z hz => ?_⟩
  have hn' : MvPolynomial.eval (G z) (a*b) ≠ 0 := (sub hz).2
  rw [map_mul] at hn'
  have h₁ := left_ne_zero_of_mul hn'
  have h₂ := right_ne_zero_of_mul hn'
  have hv := (HasValue.polynomial (p := G z) a).div (HasValue.polynomial b) h₂
  rw [hr] at hv
  exact ⟨⟨_,hv⟩, hv.evalAt ▸ div_ne_zero h₁ h₂⟩

/-- The derivative of a fraction that vanishes throughout an open set vanishes there too. -/
theorem vanishing_derivative {x : M ℂ n} (openV : IsOpen V) (sol : ∀ z ∈ V, SolvedBy v G z)
    (h : ∀ z ∈ V, HasValue (G z) x 0) : ∀ z ∈ V, HasValue (G z) (derivation ℂ v x) 0 := by
  intro z hz
  have ⟨hr,hd⟩ := hasDerivAt_evalAt (sol z hz) (show RegularAt _ _ from ⟨0,h z hz⟩)
  have he : (fun w => evalAt (G w) x) =ᶠ[𝓝 z] fun _ => 0 :=
    (openV.eventually_mem hz).mono fun w hw => (h w hw).evalAt
  have hv := hd.unique ((hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq he)
  exact hv ▸ hr.hasValue

end Model

end SympyProofs.Calculus.Antiderivative
