module

public import SympyProofs.Calculus.Antiderivative.Proof.Kind.Prim
public import SympyProofs.Calculus.Antiderivative.Proof.Liouville
public import SympyProofs.Calculus.Antiderivative.Proof.Answer
public import SympyProofs.Calculus.Antiderivative.Spec.Split

/-! Integration of a polynomial in a primitive generator, including the free constant
multiplying the generator. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Kind.Prim

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable {t : Tower R n} {lower : Level R n}

noncomputable local instance {m : ℕ} : Algebra ℤ (M k m) := Ring.toIntAlgebra _

private theorem tail_getD {α : Type} (as : List α) (i : ℕ) (d : α) :
    as.tail.getD i d = as.getD (i+1) d := by cases as <;> simp

/-- A successful reduction removes precisely a field derivative. -/
theorem reduce_sound (hs : lower.SolveSpec k t) (b : K R n) (p q : Poly (K R n)) (g : K R n)
    (hr : reduce lower b p = some (q,g)) :
    (t.step (.prim b)).modelD k (val k (K.joinPoly q)) +
      Model.includeVars (Nat.le_succ n) (val k g) = val k (K.joinPoly p) := by
  cases hc : coefficients lower b 1 p.coeffs.tail with
  | none => simp [reduce, hc] at hr
  | some pair =>
    rcases pair with ⟨v, ps⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (by simpa [reduce, hc] using hr)
    let Q := (Poly.equiv (Poly.ofList (0 :: v :: ps))).map (val k)
    let P := (Poly.equiv p).map (val k)
    let _ : Differential (M k n) := ⟨t.modelD k⟩
    have he : Extension.affine 0 (val k b) Q + C (val k (p.coeff 0 - b * v)) = P := by
      ext i
      rw [coeff_add, Extension.coeff_affine]
      cases i with
      | zero => simp [Q, P]
      | succ i =>
        have h := (coefficients_sound k hs hc).2 i
        rw [tail_getD, ← Poly.coeff_eq_getD_coeffs] at h
        simp only [Q, P, coeff_map, Poly.coeff_equiv, Poly.coeff_ofList,
          List.getD_cons_succ, coeff_C_succ, add_zero, mul_zero, zero_mul]
        change t.modelD k _ + _ * val k b * _ = _
        simpa only [show 1+i+1 = i+1+1 by omega, List.getD_cons_succ] using h
    apply (Model.stepEquiv k n).injective
    rw [map_add, Tower.stepEquiv_modelD, val_joinPoly, val_joinPoly,
      Model.stepEquiv_includeVars]
    have hd : Model.extendVariable (t.modelD k) (t.modelVelocity k (.prim b)) (algebraMap _ _ Q) =
        algebraMap _ (RatFunc (M k n)) (Extension.affine 0 (val k b) Q) := by
      simpa [Model.extendVariable, Tower.modelVelocity, Extension.affine] using
        Extension.extend_poly (Extension.affine 0 (val k b)) Q
    rw [hd, ← RatFunc.algebraMap_C, ← map_add, he]

/-- Whenever the polynomial is elementary, reduction succeeds and the residual can be
integrated below after adding some model constant times the generator velocity. -/
theorem reduce_complete (hs : lower.SolveSpec k t) (ht : t.Admissible k) (b : K R n)
    (hb : (ReducedGen.prim b).Admissible k t) (p : Poly (K R n))
    (hel : (t.step (.prim b)).Elementary k (val k (K.joinPoly p))) :
    ∃ q g d, reduce lower b p = some (q,g) ∧
      t.Elementary k (val k g + Model.C k n d * val k b) := by
  let P := (Poly.equiv p).map (val k)
  have hp := (t.elementary_prim_polynomial_iff k b ht hb P).mp (by
    rwa [← val_joinPoly, RingEquiv.symm_apply_apply])
  obtain ⟨Q, hdeg, hlow, hcoeff⟩ := hp
  have hdegP : P.natDegree = p.coeffs.tail.length := by
    simp [P, Poly.natDegree_eq]
  let w (j : ℕ) := Q.coeff (j+1)
  have hbound (j : ℕ) (hj : p.coeffs.tail.length < j) : w j = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have he (j : ℕ) : t.modelD k (w j) + ((1+j+1 : ℕ) : M k n)*val k b*w (j+1) =
      val k (p.coeffs.tail.getD j 0) := by
    rw [tail_getD, ← Poly.coeff_eq_getD_coeffs]
    by_cases hj : j ≤ P.natDegree
    · simpa only [w, show 1+j+1 = j+2 by omega, P, coeff_map, Poly.coeff_equiv] using hcoeff j hj
    · have hq : Q.natDegree < j+1 := by omega
      have hp : P.natDegree < j+1 := by omega
      have h₀ := coeff_eq_zero_of_natDegree_lt hp
      simp only [P, coeff_map, Poly.coeff_equiv] at h₀
      simp [w, coeff_eq_zero_of_natDegree_lt hq, coeff_eq_zero_of_natDegree_lt (by omega :
        Q.natDegree < j+1+1), h₀]
  obtain ⟨v,ps,c,hr,hv⟩ := coefficients_complete k hs ht hb 1 p.coeffs.tail w hbound he
  refine ⟨Poly.ofList (0 :: v :: ps), p.coeff 0 - b*v, c, by simp [reduce, hr], ?_⟩
  convert hlow using 1
  simp only [P, coeff_map, Poly.coeff_equiv, map_sub, map_mul]
  change val k v - Q.coeff 1 = _ at hv
  rw [← hv]
  ring

private theorem residual_complete (hl : lower.ElementaryBasisSpec k t) (g b : K R n) (d : k)
    (h : t.Elementary k (val k g + Model.C k n d * val k b)) :
    ∃ v, (lower.elementaryBasis [g,b]).find? (fun s => s.1.getD 0 0 != 0) = some v := by
  let bs := lower.elementaryBasis [g,b]
  cases hf : bs.find? (fun s => s.1.getD 0 0 != 0) with
  | some v => exact ⟨v, rfl⟩
  | none =>
    have hx := ((hl [g,b]).2 [1,d] rfl).mp (by simpa [Model.linearCombination] using h)
    let ev := LinearMap.proj (R := k) (φ := fun _ : Fin 2 => k) 0
    have hz : Submodule.span k
        ((fun (cs : List (K R 0)) (i : Fin 2) => Model.constantHom k (cs.getD i 0)) ''
          {cs | cs ∈ bs.map Prod.fst}) ≤ LinearMap.ker ev := Submodule.span_le.mpr (by
      rintro _ ⟨cs, hm, rfl⟩
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
      have h₀ : w.1.getD 0 0 = 0 := by simpa using List.find?_eq_none.mp hf w hw
      exact (congrArg (Model.constantHom k) h₀).trans (map_zero _))
    exact False.elim (one_ne_zero (hz hx))

/-- The triangular equations and the lower elementary subspace decide integration of a
polynomial at an admissible primitive step. -/
theorem integrate_spec (hs : lower.SolveSpec k t) (hl : lower.ElementaryBasisSpec k t)
    (ht : t.Admissible k) (b : K R n) (hb : (ReducedGen.prim b).Admissible k t) (p : Poly (K R n)) :
    match integrate lower b p with
    | .elementary a => a.Regular k ∧ a.deriv k (t.step (.prim b)) = val k (K.joinPoly p)
    | .nonelementary => ¬ (t.step (.prim b)).Elementary k (val k (K.joinPoly p)) := by
  cases hr : reduce lower b p with
  | none =>
    simp only [integrate, hr]
    intro he
    obtain ⟨q,g,d,hq,_⟩ := reduce_complete k hs ht b hb p he
    simp [hr] at hq
  | some pair =>
    rcases pair with ⟨q,g⟩
    cases hv : (lower.elementaryBasis [g,b]).find? (fun s => s.1.getD 0 0 != 0) with
    | none =>
      simp only [integrate, hr, hv]
      intro he
      obtain ⟨q',g',d,hq,hd⟩ := reduce_complete k hs ht b hb p he
      have eg : g' = g := (Prod.mk.inj (Option.some.inj (hq.symm.trans hr))).2
      subst g'
      obtain ⟨w,hw⟩ := residual_complete k hl g b d hd
      rw [hv] at hw
      cases hw
    | some pair =>
      rcases pair with ⟨cs,a⟩
      have hmem := List.mem_of_find?_eq_some hv
      obtain ⟨hlen, hreg, hd⟩ := (hl [g,b]).1 _ hmem
      obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp hlen
      have hx : x ≠ 0 := by simpa using List.find?_some hv
      simp only [integrate, hr, hv, List.getD_cons_zero, List.getD_cons_succ,
        Answer.regular_addField, Answer.regular_lift, Answer.regular_scale,
        Answer.deriv_addField, Answer.deriv_lift, Answer.deriv_scale, map_sub]
      refine ⟨hreg, ?_⟩
      have hd' : a.deriv k t =
          val k (K.ofConst x) * val k g + val k (K.ofConst y) * val k b := by
        simpa [Model.linearCombination, Model.C_constantHom] using hd
      let inc := Model.includeVars (R := k) (Nat.le_succ n)
      have dc : (t.step (.prim b)).modelD k (val k (K.ofConst (x⁻¹*y))) = 0 := by
        rw [← Model.C_constantHom, Tower.modelD_C]
      have dx : (t.step (.prim b)).modelD k (val k (K.gen : K R (n+1))) = inc (val k b) := by
        rw [← Tower.val_D, Tower.D_gen_prim, val_lift]
      have eqn := reduce_sound k hs b p q g hr
      rw [← eqn, hd', map_mul (val k) _ K.gen, Derivation.leibniz, dc, dx, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero]
      simp only [map_add, map_mul]
      simp only [← Model.C_constantHom, Model.includeVars_C, map_inv₀]
      have hn : Model.C k (n+1) (Model.constantHom k x) ≠ 0 :=
        (_root_.map_ne_zero _).mpr ((_root_.map_ne_zero _).mpr hx)
      change _ = _ + inc (val k g)
      field_simp
      ring

end SympyProofs.Calculus.Antiderivative.Kind.Prim
