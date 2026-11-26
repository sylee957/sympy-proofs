module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.MixedIndependence
public import SympyProofs.Calculus.Antiderivative.Proof.Answer
public import SympyProofs.Calculus.Antiderivative.Proof.Liouville
public import SympyProofs.Calculus.Antiderivative.Proof.ElementaryExtension

/-! Complex primitives on open sets give formal identities in the tower field. A negative
integrator verdict excludes all such primitives expressible by an answer in an elementary
extension, with arbitrary continuous logarithm branches. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n m : ℕ}

/-- An identity of derivatives on an algebraically independent complex realization gives
an identity in the formal field of the mixed tower. -/
theorem Tower.deriv_eq_of_independent {s : Tower R m} (a : Answer R m) {x : M ℂ m}
    {V : Set ℂ} {G : ℂ → Fin m → ℂ} {logs : RootSum R m → ℂ → ℂ → ℂ}
    (indep : Model.IndependentOn G V)
    (reg : ∀ z ∈ V, s.SolvedBy G z ∧ Model.RegularAt (G z) x ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z)
    (hd : ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun b c => logs b c w) (G w))
      (Model.evalAt (G z) x) z) : a.deriv ℂ s = x := by
  apply sub_eq_zero.mp
  apply indep.eq_zero
  intro z hz
  obtain ⟨hs,hx,hf,hl⟩ := reg z hz
  obtain ⟨hr, ha⟩ := a.deriv_regular_hasDerivAt hs hf hl
  simpa only [ha.unique (hd z hz), sub_self] using hr.hasValue.sub hx.hasValue

/-- An analytic identity of derivatives on a nonempty open set holds in the formal field. -/
theorem Answer.deriv_eq_of_hasDerivAt (a : Answer R n) {t : Tower R n} (ht : t.Admissible ℂ)
    {x : M ℂ n} {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty) {G : ℂ → Fin n → ℂ}
    {logs : RootSum R n → ℂ → ℂ → ℂ}
    (reg : ∀ z ∈ V, t.SolvedBy G z ∧ t.Nondegenerate (G z) ∧ Model.RegularAt (G z) x ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z)
    (hd : ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (G w))
      (Model.evalAt (G z) x) z) : a.deriv ℂ t = x := by
  exact t.deriv_eq_of_independent a
    (t.independent_of_solution ht hV hn (fun z hz => (reg z hz).1) (fun z hz => (reg z hz).2.1))
    (fun z hz => ⟨(reg z hz).1, (reg z hz).2.2⟩) hd

/-- A negative verdict excludes an analytic primitive written on an independent realization
of any elementary differential extension. Arbitrary continuous logarithm branches are allowed. -/
theorem Tower.no_function_of_independent {t : Tower R n} (ht : t.Admissible ℂ)
    {f : K R n} (h : ¬ t.Elementary ℂ (val ℂ f)) {s : Tower R m} (hs : s.Admissible ℂ)
    (inc : n ≤ m) (a : Answer R m) {V : Set ℂ} {G : ℂ → Fin m → ℂ}
    {logs : RootSum R m → ℂ → ℂ → ℂ} (indep : Model.IndependentOn G V)
    (reg : ∀ z ∈ V, s.SolvedBy G z ∧ Model.RegularAt (G z) (Model.includeVars inc (val ℂ f)) ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z) :
    letI : Differential (M ℂ n) := ⟨t.modelD ℂ⟩
    letI : Differential (M ℂ m) := ⟨s.modelD ℂ⟩
    letI : Algebra (M ℂ n) (M ℂ m) := (Model.includeVars inc).toAlgebra
    Extension.LiouvilleForm.ElementaryTower (M ℂ n) (M ℂ m) →
      ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun b c => logs b c w) (G w))
        (Model.evalAt (G z) (Model.includeVars inc (val ℂ f))) z := by
  let _ : Differential (M ℂ n) := ⟨t.modelD ℂ⟩
  let _ : Differential (M ℂ m) := ⟨s.modelD ℂ⟩
  let _ : Algebra (M ℂ n) (M ℂ m) := (Model.includeVars inc).toAlgebra
  intro ext hd
  have heq := s.deriv_eq_of_independent a indep reg hd
  have top := a.deriv_elementary ℂ s
  rw [heq] at top
  obtain ⟨ι,fi,c,hc,u,v,eqn⟩ := (s.elementary_iff_form ℂ hs _).mp top
  choose w hw using fun i => (hs (c i)).mp (hc i)
  let d (i : ι) := Model.C ℂ n (w i)
  have hd' (i : ι) : Differential.deriv (d i) = 0 := (ht _).mpr ⟨_,rfl⟩
  have hmap (i : ι) : algebraMap (M ℂ n) (M ℂ m) (d i) = c i :=
    (Model.includeVars_C ℂ inc _).trans (hw i).symm
  have hform : algebraMap (M ℂ n) (M ℂ m) (val ℂ f) =
      ∑ i, algebraMap (M ℂ n) (M ℂ m) (d i) * Differential.logDeriv (u i) +
        Differential.deriv v := by
    simp only [hmap]
    change Model.includeVars inc (val ℂ f) =
      ∑ i, c i * Differential.logDeriv (u i) + s.modelD ℂ v
    simpa only [Algebra.algebraMap_self_apply] using eqn
  obtain ⟨ι',fi',c',hc',u',v',form⟩ := ext.isLiouville.isLiouville (val ℂ f) ι d hd' u v hform
  apply h
  apply (t.elementary_iff_form ℂ ht _).mpr
  exact ⟨ι',fi',c',hc',u',v',by simpa only [Algebra.algebraMap_self_apply] using form⟩

/-- If integration reports a non-elementary integral, no answer on its own tower has the
specified analytic derivative throughout a nonempty open set. -/
theorem Tower.IntegrateSpec.no_function {t : Tower R n} {integral : K R n → Result R n}
    (hs : t.IntegrateSpec ℂ integral) (ht : t.Admissible ℂ) {f : K R n}
    (h : integral f = .nonelementary)
    (a : Answer R n) {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty) {G : ℂ → Fin n → ℂ}
    {logs : RootSum R n → ℂ → ℂ → ℂ}
    (reg : ∀ z ∈ V, t.SolvedBy G z ∧ t.Nondegenerate (G z) ∧
      Model.RegularAt (G z) (val ℂ f) ∧ Model.RegularAt (G z) (val ℂ a.field) ∧
      a.HasLogs logs G z) :
    ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (G w))
      (Model.evalAt (G z) (val ℂ f)) z := by
  intro hd
  have no := hs f
  rw [h] at no
  exact no (a.deriv_eq_of_hasDerivAt ht hV hn reg hd ▸ a.deriv_elementary ℂ t)

/-- A tower of elementary differential-field extensions descends any answer with constant
weights in the input field, after analytically identifying its derivative. -/
theorem Tower.IntegrateSpec.no_function_in_extension {t : Tower R n}
    {integral : K R n → Result R n} (hs : t.IntegrateSpec ℂ integral) (ht : t.Admissible ℂ)
    {f : K R n} (h : integral f = .nonelementary) {t' : Tower R m}
    (ht' : t'.Admissible ℂ)
    (inc : n ≤ m) (a : Answer R m) {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty)
    {G : ℂ → Fin m → ℂ} {logs : RootSum R m → ℂ → ℂ → ℂ}
    (reg : ∀ z ∈ V, t'.SolvedBy G z ∧ t'.Nondegenerate (G z) ∧
      Model.RegularAt (G z) (Model.includeVars inc (val ℂ f)) ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z) :
    letI : Differential (M ℂ n) := ⟨t.modelD ℂ⟩
    letI : Differential (M ℂ m) := ⟨t'.modelD ℂ⟩
    letI : Algebra (M ℂ n) (M ℂ m) := (Model.includeVars inc).toAlgebra
    Extension.LiouvilleForm.ElementaryTower (M ℂ n) (M ℂ m) →
      ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (G w))
        (Model.evalAt (G z) (Model.includeVars inc (val ℂ f))) z := by
  have no := hs f
  rw [h] at no
  exact t.no_function_of_independent ht no ht' inc a
    (t'.independent_of_solution ht' hV hn (fun z hz => (reg z hz).1) (fun z hz => (reg z hz).2.1))
    fun z hz => ⟨(reg z hz).1, (reg z hz).2.2⟩

/-- A negative verdict excludes analytic primitives in every admissible tower obtained
by explicitly adjoining logarithms and exponentials to the input tower. -/
theorem Tower.IntegrateSpec.no_function_of_solution {t : Tower R n}
    {integral : K R n → Result R n} (hs : t.IntegrateSpec ℂ integral) {f : K R n}
    (h : integral f = .nonelementary)
    {t' : Tower R m} (e : t.ElementaryExt t') (ht' : t'.Admissible ℂ) (a : Answer R m)
    {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty) {G : ℂ → Fin m → ℂ}
    {logs : RootSum R m → ℂ → ℂ → ℂ}
    (reg : ∀ z ∈ V, t'.SolvedBy G z ∧ t'.Nondegenerate (G z) ∧
      Model.RegularAt (G z) (Model.includeVars e.height (val ℂ f)) ∧
      Model.RegularAt (G z) (val ℂ a.field) ∧ a.HasLogs logs G z) :
    ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realizeWith (fun s c => logs s c w) (G w))
      (Model.evalAt (G z) (Model.includeVars e.height (val ℂ f))) z := by
  intro hd
  have no := hs f
  rw [h] at no
  exact no (e.descend ℂ ht' _
    (a.deriv_eq_of_hasDerivAt ht' hV hn reg hd ▸ a.deriv_elementary ℂ t'))

end SympyProofs.Calculus.Antiderivative
