module

public import SympyProofs.Calculus.Antiderivative.Proof.AnalyticField
public import SympyProofs.Calculus.Antiderivative.Spec.Analytic

/-! A regular answer differentiates to its integrand along any complex solution of the
tower equations, with any continuous local branches for its logarithms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Filter Topology

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n : ℕ}
variable {g : ℂ → Fin n → ℂ} {z : ℂ} {t : Tower R n}

/-- A regular field value that gives the complex derivative at the specified point. -/
private def RepresentsDerivative (p : Fin n → ℂ) (z : ℂ) (x : M ℂ n) (f : ℂ → ℂ) : Prop :=
  ∃ c, Model.HasValue p x c ∧ HasDerivAt f c z

namespace RepresentsDerivative

variable {p : Fin n → ℂ} {x y : M ℂ n} {f h : ℂ → ℂ}

private theorem zero : RepresentsDerivative p z 0 (fun _ => 0) :=
  ⟨0, Model.HasValue.zero, hasDerivAt_const _ _⟩

private theorem add (hf : RepresentsDerivative p z x f) (hh : RepresentsDerivative p z y h) :
    RepresentsDerivative p z (x+y) (fun w => f w + h w) := by
  obtain ⟨a,ha,ha'⟩ := hf
  obtain ⟨b,hb,hb'⟩ := hh
  exact ⟨_, ha.add hb, ha'.fun_add hb'⟩

private theorem scale (c : ℂ) (hf : RepresentsDerivative p z x f) :
    RepresentsDerivative p z (Model.C ℂ n c * x) (fun w => c * f w) := by
  obtain ⟨a,ha,ha'⟩ := hf
  exact ⟨_, (Model.HasValue.C c).mul ha, ha'.const_mul c⟩

private theorem list_sum {α : Type} (l : List α) (u : α → M ℂ n) (f : α → ℂ → ℂ)
    (h : ∀ a ∈ l, RepresentsDerivative p z (u a) (f a)) :
    RepresentsDerivative p z (l.map u).sum (fun w => (l.map fun a => f a w).sum) := by
  induction l with
  | nil => exact zero
  | cons a l ih =>
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem finset_sum {α : Type} (s : Finset α) (u : α → M ℂ n) (f : α → ℂ → ℂ)
    (h : ∀ a ∈ s, RepresentsDerivative p z (u a) (f a)) :
    RepresentsDerivative p z (∑ a ∈ s, u a) (fun w => ∑ a ∈ s, f a w) := by
  classical
  simpa only [Finset.sum_map_toList] using
    list_sum s.toList u f (fun a ha => h a (Finset.mem_toList.mp ha))

end RepresentsDerivative

/-- At a regular point the formal derivative specializes to the complex derivative. -/
theorem Answer.deriv_regular_hasDerivAt (a : Answer R n) {logs : RootSum R n → ℂ → ℂ → ℂ}
    (hg : t.SolvedBy g z) (hf : Model.RegularAt (g z) (val ℂ a.field))
    (hl : a.HasLogs logs g z) :
    Model.RegularAt (g z) (a.deriv ℂ t) ∧
      HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (g w))
        (Model.evalAt (g z) (a.deriv ℂ t)) z := by
  classical
  have top : RepresentsDerivative (g z) z (t.modelD ℂ (val ℂ a.field))
      (fun w => Model.evalAt (g w) (val ℂ a.field)) := by
    obtain ⟨hv,hd⟩ := Model.hasDerivAt_evalAt hg hf
    exact ⟨_,hv.hasValue,hd⟩
  have hs (s : RootSum R n) (hmem : s ∈ a.sums) :
      RepresentsDerivative (g z) z (s.deriv ℂ t)
        (fun w => Model.constantHom ℂ s.weight * ∑ c ∈ s.complexRoots, c * logs s c w) := by
    rw [RootSum.deriv, ← Model.C_constantHom]
    apply RepresentsDerivative.scale
    apply RepresentsDerivative.finset_sum s.complexRoots
    intro c hc
    apply RepresentsDerivative.scale
    obtain ⟨hr,hcont,he⟩ := hl s hmem c hc
    have ⟨hv,hd⟩ := Model.hasDerivAt_evalAt hg hr
    have hne : Model.evalAt (g z) (s.argAt ℂ c) ≠ 0 :=
      he.self_of_nhds ▸ Complex.exp_ne_zero _
    exact ⟨_, hv.hasValue.div hr.hasValue hne, hasDerivAt_of_exp_eq hd hcont he⟩
  obtain ⟨c,hc,hd⟩ := top.add (RepresentsDerivative.list_sum a.sums _ _ hs)
  exact ⟨⟨c,hc⟩, hc.evalAt ▸ hd⟩

/-- Any continuous choices of logarithm give the same derivative at a regular point. -/
theorem Answer.hasDerivAt_realizeWith (a : Answer R n) {logs : RootSum R n → ℂ → ℂ → ℂ}
    (hg : t.SolvedBy g z) (hf : Model.RegularAt (g z) (val ℂ a.field))
    (hl : a.HasLogs logs g z) :
    HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (g w))
      (Model.evalAt (g z) (a.deriv ℂ t)) z :=
  (a.deriv_regular_hasDerivAt hg hf hl).2

/-- On the principal branch, away from the cut, an answer has its formal derivative. -/
theorem Answer.hasDerivAt_realize (a : Answer R n)
    (hg : t.SolvedBy g z)
    (ha : a.RegularAt (g z)) :
    HasDerivAt (fun w => a.realize (g w)) (Model.evalAt (g z) (a.deriv ℂ t)) z := by
  apply a.hasDerivAt_realizeWith hg ha.1
  intro s hs c hc
  obtain ⟨hr,hcut⟩ := ha.2 s hs c hc
  have hcont := (Model.hasDerivAt_evalAt hg hr).2.continuousAt
  exact ⟨hr, hcont.clog hcut, (hcont.eventually_ne (Complex.slitPlane_ne_zero hcut)).mono
    fun _ hn => Complex.exp_log hn⟩

/-- A successful integrator with the formal specification returns a complex primitive. -/
theorem Tower.IntegrateSpec.hasDerivAt {integral : K R n → Result R n}
    (hL : t.IntegrateSpec ℂ integral) {f : K R n} {a : Answer R n} (h : integral f = .elementary a)
    (hg : t.SolvedBy g z) (ha : a.RegularAt (g z)) :
    HasDerivAt (fun w => a.realize (g w)) (Model.evalAt (g z) (val ℂ f)) z := by
  have hs := hL f
  rw [h] at hs
  rw [← hs.2]
  exact a.hasDerivAt_realize hg ha

end SympyProofs.Calculus.Antiderivative
