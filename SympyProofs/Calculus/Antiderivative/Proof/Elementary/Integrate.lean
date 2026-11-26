module

public import SympyProofs.Calculus.Antiderivative.Proof.Elementary.Add
public import SympyProofs.Calculus.Antiderivative.Proof.ElementaryParts
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.ExpIntegral
public import SympyProofs.Calculus.Antiderivative.Proof.Kind.PrimIntegral

/-! Correctness of elementary integration at a primitive or exponential tower step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Elementary

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ} (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k]

private theorem corrected_laurent (l : Poly (K R n)) (j : ℕ) (c : K R n) :
    val k (K.joinPoly (l + Poly.monomial j c) / K.gen ^ j) =
      val k (K.joinPoly l / K.gen ^ j) + val k (K.lift c) := by
  apply (Model.stepEquiv k n).injective
  simp [val_joinPoly, Model.stepEquiv_includeVars, ← C_mul_X_pow_eq_monomial, add_div,
    pow_ne_zero j (RatFunc.X_ne_zero : (RatFunc.X : RatFunc (M k n)) ≠ 0)]

variable [CharZero k] [IsAlgClosed k]

/-- Both outcomes of the single-input integration algorithm are valid over every admissible
model whenever the three lower-field routines meet their specifications. -/
theorem integrate_spec (t : Tower R n) (g : ReducedGen (K R n)) (lower : Level R n)
    (hs : lower.SolveSpec k t) (hi : lower.IntegrateSpec k t) (hb : lower.ElementaryBasisSpec k t)
    (ht : t.Admissible k) (hg : g.Admissible k t) (x : K R (n+1)) :
    match integrate t.D g lower x with
    | .elementary a => a.Regular k ∧ a.deriv k (t.step g) = val k x
    | .nonelementary => ¬ (t.step g).Elementary k (val k x) := by
  let den := x.split.2
  let j := poleOrder g den
  let p := parts t.D (g.velocity t.D) den j x.split.1
  let ds := Step.polyDer t.D (g.velocity t.D) p.normalDen
  have hd : den ≠ 0 := fun h => K.joinPoly_split_den_ne x
    (by change K.joinPoly den = 0; rw [h, ← K.joinPolyHom_apply, map_zero])
  have hp : PartsSpec k t g x.split.1 den p := parts_spec k t g hg x.split.1 den hd
  have hdecomp := hp.identity
  rw [show K.join x.split.1 den = x from K.join_split x] at hdecomp
  let L := val k (K.joinPoly p.laurent / K.gen ^ j)
  cases hl : Residue.logPart p.proper p.normalDen ds ((g.velocity t.D).coeff 1) with
  | none =>
    have hbad := Residue.logPart_complete k t g hp.residue (Model.stepEquiv k n L) hp.regular hl
    rw [RingEquiv.symm_apply_apply] at hbad
    have hex : (t.step g).Elementary k ((t.step g).modelD k (val k p.exactPart)) :=
      ⟨val k p.exactPart, [], by simp⟩
    have h : ¬ (t.step g).Elementary k (val k x) := by
      intro h
      apply hbad
      convert h.sub k hex using 1
      rw [hdecomp]
      change _ + L = _ + _ + L - _
      abel
    simpa only [integrate, den, j, p, ds, hl, Id.run, pure] using h
  | some out =>
    obtain ⟨logs,corr⟩ := out
    obtain ⟨hreg,hlogs⟩ := Residue.logPart_sound k t g hp.residue hl
    let a : Answer R (n+1) := ⟨p.exactPart,logs⟩
    let rest := p.laurent + Poly.monomial j corr
    let w := val k (K.joinPoly rest / K.gen ^ j)
    have hsum : val k x = w + a.deriv k (t.step g) := by
      rw [hdecomp, hlogs]
      change _ = val k (K.joinPoly (p.laurent + Poly.monomial j corr) / K.gen ^ j) + (_ + _)
      rw [corrected_laurent]
      abel
    let r := match g with
      | .prim b => Kind.Prim.integrate lower b rest
      | .exp u => Kind.Exp.integrate t.D u lower rest j
    have hkind : match r with
        | .elementary b => b.Regular k ∧ b.deriv k (t.step g) = w
        | .nonelementary => ¬ (t.step g).Elementary k w := by
      cases g with
      | prim b =>
        have h := Kind.Prim.integrate_spec k hs hb ht b hg rest
        cases hres : Kind.Prim.integrate lower b rest <;> rw [hres] at h <;>
          simpa only [r, w, j, poleOrder, pow_zero, div_one, hres, ReducedGen.coe_prim] using h
      | exp u =>
        have h := Kind.Exp.integrate_spec k hs hi ht u rest j
        cases hres : Kind.Exp.integrate t.D u lower rest j <;> rw [hres] at h <;>
          simpa only [r, hres, ReducedGen.coe_exp] using h
    dsimp only [ds, p, j, den] at hl
    simp only [integrate, hl, Id.run, pure]
    change match (match r with
      | .nonelementary => Result.nonelementary
      | .elementary b => .elementary (b.add a)) with
      | .elementary b => b.Regular k ∧ b.deriv k (t.step g) = val k x
      | .nonelementary => ¬ (t.step g).Elementary k (val k x)
    cases hr : r with
    | elementary b =>
      rw [hr] at hkind
      exact ⟨(b.regular_add k a).mpr ⟨hkind.1,hreg⟩, by rw [Answer.deriv_add, hkind.2, hsum]⟩
    | nonelementary =>
      rw [hr] at hkind
      intro hx
      apply hkind
      simpa [hsum] using hx.sub k (a.deriv_elementary k (t.step g))

end SympyProofs.Calculus.Antiderivative.Elementary
