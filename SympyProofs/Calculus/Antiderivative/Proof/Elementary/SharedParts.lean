module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.ResidueRows
public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Directions

/-! Hermite reduction over a common denominator commutes with taking combinations of its columns
at the level of the represented rational functions. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

noncomputable local instance : Algebra ℤ (M k (n+1)) := Ring.toIntAlgebra _

private theorem hermiteLoop_den {F : Type} [Field F] [DecidableEq F] (D : F → F) (dx s : Poly F)
    (fuel : ℕ) (a b m : Poly F) :
    (Step.hermiteLoop D dx s fuel a m).denominator =
      (Step.hermiteLoop D dx s fuel b m).denominator := by
  induction fuel generalizing a b m with
  | zero => rfl
  | succ fuel ih =>
    simp only [Step.hermiteLoop]
    split
    · rfl
    · exact ih _ _ _

private theorem parts_den (t : Tower R n) (dx den : Poly (K R n)) (j : ℕ)
    (a b : Poly (K R n)) :
    (parts t.D dx den j a).normalDen = (parts t.D dx den j b).normalDen := by
  have h : (Step.separatePole a den j).normalDen = (Step.separatePole b den j).normalDen := by
    by_cases hj : j = 0 <;> simp [Step.separatePole, hj]
  simp only [parts, h, Step.hermite]
  split
  · rfl
  · exact hermiteLoop_den ..

/-- The normal and Laurent terms of a constant-linear combination of Hermite columns. -/
structure SharedParts (t : Tower R n) (g : ReducedGen (K R n)) (gs : List (K R (n+1))) (j : ℕ)
    (s : Poly (K R n)) (ps : List (Parts R n)) : Prop where
  squarefree : Squarefree (Step.modelPoly (val k) s)
  normal : ∀ q : (M k n)[X], Prime q → q ∣ Step.modelPoly (val k) s → ¬ q ∣ t.polyDerModel k g q
  coprime : IsCoprime ((X : (M k n)[X]) ^ j) (Step.modelPoly (val k) s)
  proper : ∀ p ∈ ps, (Step.modelPoly (val k) p.proper).degree < (Step.modelPoly (val k) s).degree
  identity : ∀ cs : List k, Model.linearCombination k cs gs =
    (t.step g).modelD k (Model.linearCombination k cs (ps.map Parts.exactPart)) +
    (Model.stepEquiv k n).symm
      (algebraMap (M k n)[X] _ (Model.polynomialCombination k cs (ps.map Parts.proper)) /
        algebraMap (M k n)[X] _ (Step.modelPoly (val k) s)) +
    laurentValue k j (Model.polynomialCombination k cs (ps.map Parts.laurent))

private theorem combine_parts (t : Tower R n) (g : ReducedGen (K R n)) (j : ℕ)
    (s : Poly (K R n)) (gs : List (K R (n+1))) (ps : List (Parts R n)) (cs : List k)
    (h : List.Forall₂ (fun x (p : Parts R n) => val k x =
      (t.step g).modelD k (val k p.exactPart) + val k (K.join p.proper s) +
        val k (K.joinPoly p.laurent / K.gen ^ j)) gs ps) :
    Model.linearCombination k cs gs =
      (t.step g).modelD k (Model.linearCombination k cs (ps.map Parts.exactPart)) +
      (Model.stepEquiv k n).symm
        (algebraMap (M k n)[X] _ (Model.polynomialCombination k cs (ps.map Parts.proper)) /
          algebraMap (M k n)[X] _ (Step.modelPoly (val k) s)) +
      laurentValue k j (Model.polynomialCombination k cs (ps.map Parts.laurent)) := by
  induction h generalizing cs with
  | nil => cases cs <;> simp [Model.linearCombination, Model.polynomialCombination, laurentValue]
  | @cons x p xs ps h _ ih =>
    cases cs with
    | nil => simp [Model.linearCombination, Model.polynomialCombination, laurentValue]
    | cons c cs =>
      simp only [List.map_cons, Model.linearCombination, Model.polynomialCombination, map_add,
        Derivation.leibniz, Tower.modelD_C, smul_eq_mul, mul_zero, add_zero]
      rw [h, ih]
      apply (Model.stepEquiv k n).injective
      simp only [K.join, map_add, map_mul, map_div₀, map_pow, Model.stepEquiv_scalar,
        RingEquiv.apply_symm_apply, laurentValue, val_joinPoly, val_gen, Model.stepEquiv_last,
        Model.coefficientPolynomial, Step.modelPoly_apply, RatFunc.algebraMap_C]
      ring

/-- All columns prepared by the executable basis routine satisfy the shared Hermite identity. -/
theorem sharedParts_spec [CharZero k] (t : Tower R n) (g : ReducedGen (K R n))
    (hg : g.Admissible k t)
    (gs : List (K R (n+1))) :
    let (as,den) := commonDen gs
    let j := poleOrder g den
    let ps := as.map (parts t.D (g.velocity t.D) den j)
    let s := (ps.head?.map Parts.normalDen).getD 1
    SharedParts k t g gs j s ps := by
  let den := (commonDen gs).2
  let j := poleOrder g den
  let build := parts t.D (g.velocity t.D) den j
  let as := (commonDen gs).1
  let ps := as.map build
  let s := (ps.head?.map Parts.normalDen).getD 1
  change SharedParts k t g gs j s ps
  have hd : den ≠ 0 := (commonDen_spec k gs).1
  have hp (a : Poly (K R n)) : PartsSpec k t g a den (build a) := parts_spec k t g hg _ _ hd
  have hden : ∀ a ∈ as, (build a).normalDen = s := by
    intro a ha
    rcases has : as with _ | ⟨b, bs⟩
    · simp [has] at ha
    · simpa [s, ps, has] using parts_den t (g.velocity t.D) den j a b
  have hgeom : Squarefree (Step.modelPoly (val k) s) ∧
      (∀ q : (M k n)[X], Prime q → q ∣ Step.modelPoly (val k) s → ¬ q ∣ t.polyDerModel k g q) ∧
      IsCoprime ((X : (M k n)[X]) ^ j) (Step.modelPoly (val k) s) := by
    cases has : as with
    | nil =>
      simp [s, ps, has, isCoprime_one_right]
      exact fun _ hq h => (hq.not_dvd_one h).elim
    | cons a as =>
      rw [← hden a (by simp [has])]
      exact ⟨(hp a).residue.squarefree, (hp a).residue.normal, (hp a).coprime⟩
  refine ⟨hgeom.1,hgeom.2.1,hgeom.2.2,?_,?_,⟩
  · intro p h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    rw [← hden a ha]
    exact (hp a).residue.proper
  · intro cs
    apply combine_parts k t g j s gs ps cs
    obtain ⟨hzn,hnum⟩ := commonDen_numerators gs
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_of_length_eq_of_get hnum.length_eq
    intro i h₁ h₂
    let a := as.get ⟨i,h₂⟩
    have hx : K.join a den = gs.get ⟨i,h₁⟩ := (div_eq_iff hzn).mpr (hnum.get h₁ h₂)
    change val k (gs.get _) = _ + val k (K.join (build a).proper s) + _
    rw [← hx, ← hden a (List.get_mem ..)]
    exact (hp a).identity

end SympyProofs.Calculus.Antiderivative.Elementary
