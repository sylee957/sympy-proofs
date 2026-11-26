module

public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.OpenSet
public import SympyProofs.Calculus.Antiderivative.Proof.Analytic.Relation
public import SympyProofs.Calculus.Antiderivative.Proof.ConstantsConverse

/-! On a nonempty open set, complex solutions of an admissible tower's equations are
algebraically independent, provided its exponential generators never vanish. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Algebra R ℂ] [FaithfulSMul R ℂ] {n : ℕ}

namespace Model

/-- Include a polynomial in the newest variable in the next model field. -/
private noncomputable def adjoinPoly : (M ℂ n)[X] →+* M ℂ (n+1) :=
  (stepEquiv ℂ n).symm.toRingHom.comp (algebraMap _ _)

private theorem adjoin_C (a : M ℂ n) :
    adjoinPoly (Polynomial.C a) = includeVars (Nat.le_succ n) a := by
  apply (stepEquiv ℂ n).injective
  simp [adjoinPoly, stepEquiv_includeVars]

private theorem adjoin_X : adjoinPoly (X : (M ℂ n)[X]) =
    polynomial ℂ (MvPolynomial.X (Fin.last n)) := by
  apply (stepEquiv ℂ n).injective
  simp [adjoinPoly, stepEquiv_last]

private theorem hasValue_pow {m : ℕ} {p : Fin m → ℂ} {v : M ℂ m} {c : ℂ}
    (h : HasValue p v c) (j : ℕ) : HasValue p (v^j) (c^j) := by
  induction j with
  | zero => simpa using (HasValue.C (p := p) (1 : ℂ))
  | succ j ih => simpa only [pow_succ] using ih.mul h

private theorem no_relation {t : Tower R n} {g : ReducedGen (K R n)} (hg : g.Admissible ℂ t)
    {G : ℂ → Fin (n+1) → ℂ} {V : Set ℂ} (sol : ∀ z ∈ V, (t.step g).SolvedBy G z)
    (nz : ∀ z ∈ V, (t.step g).Nondegenerate (G z))
    (indep : ∀ W ⊆ V, IsOpen W → W.Nonempty → IndependentOn (lower G) W) :
    ∀ (d : ℕ) (q : (M ℂ n)[X]), q.natDegree = d →
      ∀ W ⊆ V, IsOpen W → W.Nonempty → (∀ z ∈ W, HasValue (G z) (adjoinPoly q) 0) → q = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro q hdeg W hWV hW hnW hq
    by_contra hn
    have hl := leadingCoeff_ne_zero.mpr hn
    by_cases zd : q.natDegree = 0
    · have eqn := eq_C_of_natDegree_eq_zero zd
      have hc : q.coeff 0 = 0 := (indep W hWV hW hnW).eq_zero fun z hz => by
        have h := hq z hz
        rw [eqn,adjoin_C] at h
        exact hasValue_include_iff.mp h
      exact hn (by rw [eqn,hc,C_0])
    let m := q * Polynomial.C q.leadingCoeff⁻¹
    have hm : m.Monic := monic_mul_leadingCoeff_inv hn
    have hdegree : m.natDegree = d := (natDegree_mul_C (inv_ne_zero hl)).trans hdeg
    have lowerSol (z : ℂ) (hz : z ∈ V) := (sol z hz).lower
    obtain ⟨U,hoU,hnU,hUW,hu⟩ :=
      (indep W hWV hW hnW).exists_regular (inv_ne_zero hl) hW fun z hz => lowerSol z (hWV hz)
    have hm₀ (z : ℂ) (hz : z ∈ U) : HasValue (G z) (adjoinPoly m) 0 := by
      rw [show m = _ from rfl,map_mul,adjoin_C]
      simpa only [zero_mul] using
        (hq z (hUW hz)).mul (hasValue_include_iff.mpr (hu z hz).1.hasValue)
    let c := (m.natDegree : M ℂ n) * val ℂ ((g.velocity t.D).coeff 1)
    obtain ⟨S,hoS,hnS,hSU,hs⟩ : ∃ S : Set ℂ, IsOpen S ∧ S.Nonempty ∧ S ⊆ U ∧
        ∀ z ∈ S, RegularAt (lower G z) c := by
      by_cases hc : c = 0
      · exact ⟨U,hoU,hnU,fun _ a => a,fun z _ => hc ▸ ⟨0,HasValue.zero⟩⟩
      · obtain ⟨S,hoS,hnS,hSU,hs⟩ := (indep U (hUW.trans hWV) hoU hnU).exists_regular hc hoU
          fun z hz => lowerSol z (hWV (hUW hz))
        exact ⟨S,hoS,hnS,hSU,fun z hz => (hs z hz).1⟩
    let r := t.polyDerModel ℂ g m - Polynomial.C c * m
    have hr (z : ℂ) (hz : z ∈ S) : HasValue (G z) (adjoinPoly r) 0 := by
      have hd := vanishing_derivative hoU (fun w hw => sol w (hWV (hUW hw))) hm₀ z (hSU hz)
      change HasValue (G z) ((t.step g).modelD ℂ (adjoinPoly m)) 0 at hd
      have hc := (hasValue_include_iff.mpr (hs z hz).hasValue).mul (hm₀ z (hSU hz))
      simp only [mul_zero] at hc
      have hder : adjoinPoly (t.polyDerModel ℂ g m) = (t.step g).modelD ℂ (adjoinPoly m) :=
        (t.modelD_adjoinPoly ℂ g m).symm
      simpa only [r, map_sub, map_mul, hder, adjoin_C, sub_zero] using hd.sub hc
    have hr0 : r = 0 := by
      by_contra hne
      have hdegree' := t.degree_polyDerModel ℂ g hm
      change r.degree < m.degree at hdegree'
      rw [degree_eq_natDegree hne,degree_eq_natDegree hm.ne_zero, Nat.cast_lt, hdegree] at hdegree'
      exact hne (ih _ hdegree' r rfl S (hSU.trans (hUW.trans hWV)) hoS hnS hr)
    obtain ⟨u,hg',pow⟩ := t.monic_relation hg hm (by omega) (sub_eq_zero.mp hr0)
    subst g
    obtain ⟨z,hz⟩ := hnU
    have hv := hm₀ z hz
    rw [pow,map_pow,adjoin_X] at hv
    have hv' := hasValue_pow
      (HasValue.polynomial (p := G z) (MvPolynomial.X (Fin.last n))) m.natDegree
    rw [MvPolynomial.eval_X] at hv'
    exact pow_ne_zero _ (nz z (hWV (hUW hz))).2 (hv'.unique hv)

end Model

/-- The coordinates of a complex solution satisfy no polynomial relation on an open set. -/
theorem Tower.independent_of_solution_reduced (t : Tower R n) (hf : t.TangentFree)
    (ht : t.Admissible ℂ)
    {G : ℂ → Fin n → ℂ} {V : Set ℂ} (hV : IsOpen V) (hn : V.Nonempty)
    (sol : ∀ z ∈ V, t.SolvedBy G z) (nz : ∀ z ∈ V, t.Nondegenerate (G z)) :
    Model.IndependentOn G V := by
  induction t, hf using Tower.tangentFree_induct generalizing V with
  | base =>
    intro p hp
    obtain ⟨z,hz⟩ := hn
    have h := hp z hz
    rw [MvPolynomial.eq_C_of_isEmpty p] at h ⊢
    rw [MvPolynomial.eval_C] at h
    rw [h,map_zero]
  | @step n t g _ ih =>
    obtain ⟨lowerAdm, genAdm⟩ := (t.admissible_step_iff ℂ g).mp ht
    have below (W : Set ℂ) (hw : W ⊆ V) (ho : IsOpen W) (hne : W.Nonempty) :=
      ih lowerAdm ho hne (fun z hz => (sol z (hw hz)).lower) fun z hz => (nz z (hw hz)).lower
    intro p hp
    let q := (Model.splitPolynomial ℂ n p).map (algebraMap _ (M ℂ n))
    have e : Model.adjoinPoly q = Model.polynomial ℂ p := by
      apply (Model.stepEquiv ℂ n).injective
      rw [Model.stepEquiv_polynomial]
      simp [Model.adjoinPoly,q]
    have hq : q = 0 := Model.no_relation genAdm sol nz below _ q rfl V (fun _ a => a) hV hn
      fun z hz => e ▸ hp z hz ▸ Model.HasValue.polynomial p
    apply IsFractionRing.injective _ (M ℂ (n+1))
    change Model.polynomial ℂ p = Model.polynomial ℂ 0
    rw [← e,hq,map_zero]
    exact (map_zero _).symm

end SympyProofs.Calculus.Antiderivative
