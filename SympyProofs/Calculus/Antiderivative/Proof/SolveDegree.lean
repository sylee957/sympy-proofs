module

public import SympyProofs.Calculus.Antiderivative.Proof.Solve.Descend
public import SympyProofs.Calculus.Antiderivative.Proof.SolveBounds

/-! The two leading coefficient equations bound the degree of a polynomial solution. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable [NatBound (K R 0)] [LawfulNatBound (K R 0)]

noncomputable local instance : Algebra ℤ (M k n) := Ring.toIntAlgebra _

omit [CharZero k] in
/-- The scalar multiple in a limited primitive is unique when b has no primitive below. -/
theorem limited_degree (t : Tower R n) (L : Level R n) (hs : L.SolveSpec k t) (q b : K R n)
    (hb : (ReducedGen.prim b).Admissible k t) (j : ℕ) (z : M k n)
    (he : t.modelD k z = val k q - j * val k b) :
    j ≤ ((L.limited q b).map fun v => NatBound.natBound v.1).getD 0 := by
  cases h : L.limited q b with
  | none =>
    exact False.elim ((Level.limited_complete k hs h) ⟨(j : k), z, by simpa using he⟩)
  | some p =>
    obtain ⟨c,y⟩ := p
    have hy := Level.limited_sound k hs h
    suffices c = j from LawfulNatBound.natBound_spec c j this
    apply (val (n := n) k).injective.comp K.ofConst.injective |>.eq_iff.mp
    simp only [Function.comp_apply, map_natCast]
    by_contra hne
    apply hb
    let v := val k (K.ofConst (n := n) c)
    have hv : v - (j : M k n) ≠ 0 := sub_ne_zero.mpr hne
    have hz : t.modelD k (v - (j : M k n)) = 0 := by
      change t.modelD k (val k (K.ofConst c) - (j : M k n)) = 0
      rw [map_sub, ← Model.C_constantHom, Tower.modelD_C, Derivation.map_natCast, sub_zero]
    refine ⟨(z - val k y) / (v - j), ?_⟩
    rw [Derivation.leibniz_div_const _ _ _ hz, smul_eq_mul, inv_mul_eq_div, map_sub, he, hy,
      div_eq_iff hv, map_mul]
    dsimp [v]
    ring

omit [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)] in
private theorem twist_prim (t : Tower R n) (b : K R n) :
    val k (((ReducedGen.prim b).velocity t.D).coeff 1) = 0 := by
  have h := congrArg (fun p : (M k n)[X] => p.coeff 1)
    (Tower.modelPoly_velocity k t (.prim b))
  simpa [ReducedGen.velocity, Tower.modelVelocity] using h

omit [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)] in
private theorem twist_exp (t : Tower R n) (b : K R n) :
    val k (((ReducedGen.exp b).velocity t.D).coeff 1) = val k (t.D b) := by
  have h := congrArg (fun p : (M k n)[X] => p.coeff 1) (Tower.modelPoly_velocity k t (.exp b))
  simpa [ReducedGen.velocity, Tower.modelVelocity] using h

omit [CharZero k] [LawfulNatBound (K R 0)] in
/-- A polynomial solution at an exponential step has degree below the exceptional logarithmic
slope or below the size bound of its right-hand side. -/
theorem degree_exp (t : Tower R n) (u : K R n) (hu : (ReducedGen.exp u).Admissible k t)
    (L : Level R n) (hl : L.LogRelationsSpec k t) (a b : Poly (K R n)) (d size : ℕ)
    (ha : a.natDegree ≤ d) (hb : b.natDegree ≤ d) (hab : a.coeff d = 0 → b.coeff d ≠ 0)
    (p : (M k n)[X]) (hs : Below size (operator k t (.exp u) a b p)) :
    Below (degreeBound t.D (.exp u) L a b d size) p := by
  intro j hj
  by_cases hzero : p = 0
  · simp [hzero]
  apply coeff_eq_zero_of_natDegree_lt
  by_contra hg
  let m := p.natDegree
  have big : degreeBound t.D (.exp u) L a b d size ≤ m := le_trans hj (Nat.le_of_not_gt hg)
  have hsize : size ≤ m := by
    by_cases hr : a.coeff d = 0
    · simpa [degreeBound, hr] using big
    · exact (le_max_left _ _).trans (by simpa only [degreeBound, ite_eq_right hr] using big)
  have hp : p.coeff m ≠ 0 := leadingCoeff_ne_zero.mpr hzero
  have top := (operator_top k t (.exp u) a b d m ha hb p le_rfl).symm
  rw [hs _ (by omega)] at top
  simp only [map_add, map_mul, map_natCast, twist_exp] at top
  by_cases hr : a.coeff d = 0
  · exfalso
    simp [hr, hab hr, hp] at top
  · have hval : val k (a.coeff d) ≠ 0 := (_root_.map_ne_zero _).mpr hr
    have hlog : t.SaturatedLog k (val k (b.coeff d / a.coeff d + (m : K R n) * t.D u)) := by
      refine ⟨1, (p.coeff m)⁻¹, Nat.one_pos, inv_ne_zero hp, ?_⟩
      rw [Derivation.leibniz_inv]
      simp only [Nat.cast_one, one_mul, smul_eq_mul, map_add, map_mul, map_div₀, map_natCast]
      field_simp
      linear_combination -top
    have bound := L.exponentBound_spec k t hl u _ hu m hlog
    rw [degreeBound, ite_eq_right hr] at big
    omega

/-- The coefficient just below the highest possible one of a product. -/
private theorem coeff_mul_second {F : Type*} [Field F] {P Z : F[X]} {lam a : ℕ}
    (hP : P.natDegree ≤ lam) (hZ : Z.natDegree ≤ a + 1) :
    (P * Z).coeff (lam + a) =
      P.coeff lam * Z.coeff a + (if lam = 0 then 0 else P.coeff (lam - 1)) * Z.coeff (a + 1) := by
  cases lam with
  | zero =>
    rw [eq_C_of_natDegree_le_zero hP]
    simp
  | succ l =>
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : F[X], P₁ = P - C (P.coeff (l + 1)) * X ^ (l + 1) := ⟨_, rfl⟩
    have deg : P₁.natDegree ≤ l := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      rw [hP₁, coeff_sub, coeff_C_mul, coeff_X_pow]
      rcases (Nat.succ_le_of_lt hi).eq_or_lt with e | lt
      · rw [← e]
        simp
      · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt lt), ite_eq_right (by omega)]
        simp
    have split : P = C (P.coeff (l + 1)) * X ^ (l + 1) + P₁ := by rw [hP₁]; ring
    have low : P₁.coeff l = P.coeff l := by
      rw [hP₁, coeff_sub, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega)]
      simp
    have e1 : (C (P.coeff (l + 1)) * X ^ (l + 1) * Z).coeff (l + 1 + a) =
        P.coeff (l + 1) * Z.coeff a := by
      rw [mul_assoc, coeff_C_mul, add_comm (l + 1) a, coeff_X_pow_mul]
    have e2 : (P₁ * Z).coeff (l + 1 + a) = P.coeff l * Z.coeff (a + 1) := by
      rw [show l + 1 + a = l + (a + 1) by omega, coeff_mul_add_eq_of_natDegree_le deg hZ, low]
    conv_lhs => rw [split, add_mul, coeff_add, e1, e2]
    simp

omit [CharZero k] [NatBound (K R 0)] [LawfulNatBound (K R 0)] in
private theorem prim_coeff (t : Tower R n) (v : K R n) (p : (M k n)[X]) (i : ℕ) :
    (t.polyDerModel k (.prim v) p).coeff i = t.modelD k (p.coeff i) +
      ((i+1 : ℕ) : M k n) * val k v * p.coeff (i+1) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have he : t.polyDerModel k (.prim v) = Extension.affine 0 (val k v) := by
    simp [Tower.polyDerModel, Tower.modelVelocity, Extension.affine]
  rw [he, Extension.coeff_affine]
  simp
  rfl

omit [CharZero k] in
/-- If a polynomial solution is larger than the right-hand side at a primitive step, its
two highest coefficients give a limited primitive that fixes its degree. -/
theorem degree_prim (t : Tower R n) (v : K R n) (hv : (ReducedGen.prim v).Admissible k t)
    (L : Level R n) (hl : L.SolveSpec k t) (a b : Poly (K R n)) (d size : ℕ)
    (ha : a.natDegree ≤ d) (hb : b.natDegree ≤ d) (hab : a.coeff d = 0 → b.coeff d ≠ 0)
    (p : (M k n)[X]) (hs : Below size (operator k t (.prim v) a b p)) :
    Below (degreeBound t.D (.prim v) L a b d size) p := by
  intro index hidx
  apply coeff_eq_zero_of_natDegree_lt
  by_contra hge
  have big : degreeBound t.D (.prim v) L a b d size ≤ p.natDegree :=
    le_trans hidx (Nat.le_of_not_gt hge)
  have hsize : size + 2 ≤ p.natDegree := by
    by_cases hr : a.coeff d = 0
    · simpa [degreeBound, hr] using big
    · exact (le_max_left _ _).trans (by simpa only [degreeBound, ite_eq_right hr] using big)
  obtain ⟨j,hj⟩ : ∃ j, p.natDegree = j+1 := ⟨p.natDegree-1, by omega⟩
  have hn : p ≠ 0 := fun h => by simp [h] at hj
  have hp : p.coeff (j+1) ≠ 0 := by rw [← hj]; exact leadingCoeff_ne_zero.mpr hn
  have top := (operator_top k t (.prim v) a b d (j+1) ha hb p hj.le).symm
  rw [hs _ (by omega)] at top
  simp only [map_add, map_mul, twist_prim, mul_zero, zero_mul, add_zero] at top
  by_cases hr : a.coeff d = 0
  · exfalso
    simp [hr, hab hr, hp] at top
  · let A := modelPoly k a
    let B := modelPoly k b
    have hA : A.natDegree ≤ d := by simpa [A, modelPoly] using ha
    have hB : B.natDegree ≤ d := by simpa [B, modelPoly] using hb
    have h0 : A.coeff d ≠ 0 := by simpa [A, modelPoly] using hr
    have mid := hs (d+j) (by omega)
    change (A * t.polyDerModel k (.prim v) p + B * p).coeff (d+j) = 0 at mid
    have hD := (natDegree_der_le k t (.prim v) p).trans hj.le
    simp only [ReducedGen.coe_prim] at hD
    rw [coeff_add, coeff_mul_second hA hD,
      coeff_mul_second hB hj.le, prim_coeff, prim_coeff,
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < (j+1)+1)] at mid
    simp only [mul_zero, add_zero] at mid
    have ca (i : ℕ) : val k (a.coeff i) = A.coeff i := by simp [A, modelPoly]
    have cb (i : ℕ) : val k (b.coeff i) = B.coeff i := by simp [B, modelPoly]
    rw [ca, cb] at top
    have h1 : t.modelD k (p.coeff (j+1)) = -(B.coeff d * p.coeff (j+1)) / A.coeff d := by
      rw [eq_div_iff h0]
      linear_combination top
    have h2 : t.modelD k (p.coeff j) =
        (-((if d = 0 then 0 else A.coeff (d-1)) * t.modelD k (p.coeff (j+1))) -
          B.coeff d * p.coeff j - (if d = 0 then 0 else B.coeff (d-1)) * p.coeff (j+1)) /
          A.coeff d - ((j+1 : ℕ) : M k n) * val k v * p.coeff (j+1) := by
      rw [eq_sub_iff_add_eq, eq_div_iff h0]
      linear_combination mid
    have key : t.modelD k (p.coeff j / p.coeff (j+1)) =
        val k (cancellation a b d) - ((j+1 : ℕ) : M k n) * val k v := by
      rw [Derivation.leibniz_div]
      simp only [smul_eq_mul, h2, h1]
      by_cases hd : d = 0
      · simp only [hd, ↓reduceIte, cancellation, map_zero, zero_mul, zero_sub] at *
        field_simp
        ring
      · simp only [cancellation, ite_eq_right hd, map_div₀, map_pow, map_mul, map_sub]
        simp only [ca, cb]
        field_simp
        ring
    have hbound := limited_degree k t L hl _ _ hv _ _ key
    simp only [degreeBound, ite_eq_right hr] at big
    omega

end SympyProofs.Calculus.Antiderivative.Solve
