module

public import SympyProofs.Calculus.Antiderivative.Proof.Poles
public import SympyProofs.Calculus.Antiderivative.Proof.SolveBounds
public import SympyProofs.Calculus.Antiderivative.Extension.Pole

/-! The special pole and the universal denominator of the flat-field Risch equation. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Solve

open Polynomial
open scoped Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}
variable (t : Tower R n) (u : K R n)

noncomputable local instance poleOrdersIntAlgebra : Algebra ℤ (M k n) := Ring.toIntAlgebra _

omit [CharZero k] in
private theorem exp_coeff (p : (M k n)[X]) (i : ℕ) :
    (t.polyDerModel k (.exp u) p).coeff i =
      t.modelD k (p.coeff i) + (i : M k n) * val k (t.D u) * p.coeff i := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  have h : t.polyDerModel k (.exp u) = Extension.affine (val k (t.D u)) 0 := by
    simp [Tower.polyDerModel, Tower.modelVelocity, Extension.affine]
  rw [h, Extension.coeff_affine]
  simp
  rfl

omit [CharZero k] in
private theorem exp_power (i : ℕ) :
    t.polyDerModel k (.exp u) (X ^ i) = C ((i : M k n) * val k (t.D u)) * X ^ i := by
  ext j
  rw [exp_coeff, coeff_C_mul, coeff_X_pow]
  split <;> simp_all

omit [CharZero k] in
private theorem exp_coeff_zero (p : (M k n)[X]) :
    (t.polyDerModel k (.exp u) p).coeff 0 = t.modelD k (p.coeff 0) := by
  simp [exp_coeff]

omit [CharZero k] in
/-- At the generator of an exponential step, a pole of the solution deeper than that of the
right-hand side gives a field element with the indicated logarithmic derivative. -/
theorem special_order {N B H T v d : (M k n)[X]} (hT : T ≠ 0) (hd : d ≠ 0)
    (hu : IsRelPrime v d) (cop : IsCoprime N B)
    (he : Extension.Pole.Equation (t.polyDerModel k (.exp u)) N B H T v d) :
    multiplicity X d ≤ multiplicity X T ∨ (B.coeff 0 ≠ 0 ∧ ∃ A : M k n, A ≠ 0 ∧
      t.modelD k A = ((multiplicity X d : M k n) * val k (t.D u) -
        N.coeff 0 / B.coeff 0) * A) := by
  by_cases hle : multiplicity X d ≤ multiplicity X T
  · exact Or.inl hle
  right
  obtain ⟨d₁, hd₁, hXd⟩ :=
    (FiniteMultiplicity.of_prime_left prime_X hd).exists_eq_pow_mul_and_not_dvd
  obtain ⟨T₁, hT₁, hXT⟩ :=
    (FiniteMultiplicity.of_prime_left prime_X hT).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity X d = a at hd₁ hle ⊢
  generalize multiplicity X T = m at hT₁ hle
  obtain ⟨j, rfl⟩ : ∃ j, a = m + j + 1 := ⟨a - m - 1, by omega⟩
  have δd : t.polyDerModel k (.exp u) d = X ^ (m + j + 1) *
      (C (((m + j + 1 : ℕ) : M k n) * val k (t.D u)) * d₁ +
        t.polyDerModel k (.exp u) d₁) := by
    rw [hd₁, Derivation.leibniz, exp_power]
    simp only [smul_eq_mul]
    ring
  obtain ⟨W, hW⟩ : ∃ W, W = (t.polyDerModel k (.exp u) v * d₁ -
      v * (C (((m + j + 1 : ℕ) : M k n) * val k (t.D u)) * d₁ +
        t.polyDerModel k (.exp u) d₁)) * B + N * v * d₁ := ⟨_, rfl⟩
  have key : W * T₁ = H * X ^ (j + 1) * d₁ ^ 2 * B := by
    apply mul_left_cancel₀ (pow_ne_zero (m + j + 1 + m) (X_ne_zero (R := M k n)))
    unfold Extension.Pole.Equation at he
    rw [δd, hd₁, hT₁] at he
    rw [hW]
    simp only [pow_add, pow_succ] at he ⊢
    linear_combination he
  have XW : X ∣ W := by
    have h : X ∣ W * T₁ := by
      rw [key, pow_succ]
      exact ⟨H * X ^ j * d₁ ^ 2 * B, by ring⟩
    exact (prime_X.dvd_mul.mp h).resolve_right hXT
  have W0 := X_dvd_iff.mp XW
  have Xd : (X : (M k n)[X]) ∣ d := by
    rw [hd₁, pow_succ]
    exact ⟨X ^ (m + j) * d₁, by ring⟩
  have v0 : v.coeff 0 ≠ 0 := fun z => not_isUnit_X (hu (X_dvd_iff.mpr z) Xd)
  have d0 : d₁.coeff 0 ≠ 0 := fun z => hXd (X_dvd_iff.mpr z)
  rw [hW] at W0
  simp only [coeff_add, coeff_sub, mul_coeff_zero, exp_coeff_zero, coeff_C_zero] at W0
  have B0 : B.coeff 0 ≠ 0 := by
    intro z
    rw [z, mul_zero, zero_add] at W0
    have N0 : N.coeff 0 = 0 := by
      rcases mul_eq_zero.mp W0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact (v0 h).elim
      · exact (d0 h).elim
    exact not_isUnit_X (cop.isUnit_of_dvd' (X_dvd_iff.mpr N0) (X_dvd_iff.mpr z))
  refine ⟨B0, v.coeff 0 / d₁.coeff 0, div_ne_zero v0 d0, ?_⟩
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  field_simp
  linear_combination W0

/-- The universal denominator computed by the solver contains the denominator of every
reduced rational solution, for arbitrary constant-linear right-hand sides. -/
theorem denominator_dvd [NatBound (K R 0)] [LawfulNatBound (K R 0)] (g : ReducedGen (K R n))
    (hg : g.Admissible k t) (lower : Level R n) (hl : lower.LogRelationsSpec k t)
    (a b d : Poly (K R n)) (hb : b ≠ 0) (hd : d ≠ 0)
    (hc : IsCoprime (Step.modelPoly (val k) b) (Step.modelPoly (val k) a))
    (y : RatFunc (M k n)) (h : (M k n)[X])
    (he : Extension.Pole.Equation (t.polyDerModel k g) (Step.modelPoly (val k) a)
      (Step.modelPoly (val k) b) h (Step.modelPoly (val k) d) y.num y.denom) :
    y.denom ∣ Step.modelPoly (val k) (Poly.X ^ special t.D g lower a b d * d *
      b ^ normalBound a b (Step.polyDer t.D (g.velocity t.D) b)) := by
  let f := Step.modelPoly (val (R := R) (n := n) k)
  have hf : Function.Injective f :=
    (Polynomial.map_injective _ (val_injective k)).comp Poly.equiv.injective
  have hb' := (map_ne_zero_iff f hf).mpr hb
  have hd' := (map_ne_zero_iff f hf).mpr hd
  let bound := normalBound a b (Step.polyDer t.D (g.velocity t.D) b)
  have res (s : (M k n)[X]) (i : ℕ) (hs : Prime s) (hsb : s ∣ f b)
      (hsr : s ∣ f a - C (i : M k n) * t.polyDerModel k g (f b)) : i ≤ bound := by
    have deg := natDegree_le_of_dvd hsb hb'
    have dn : b.natDegree ≠ 0 := by
      have : (f b).natDegree = b.natDegree := by simp [f, natDegree_map]
      have := hs.irreducible.natDegree_pos
      omega
    apply le_normalBound k _ _ _ dn hc
    intro cp
    rw [t.modelPoly_polyDer k g b] at cp
    exact hs.not_isUnit (cp.isUnit_of_dvd' hsb hsr)
  change y.denom ∣ f (Poly.X ^ _ * d * b ^ bound)
  simp only [map_mul, map_pow, show f Poly.X = X by simp [f], mul_assoc]
  cases g with
  | prim v =>
    rw [special, pow_zero, one_mul]
    exact Extension.Pole.denominator_dvd _ (fun s hs => t.prime_normal_prim k v hg hs)
      hb' hd' y.denom_ne_zero y.isCoprime_num_denom.isRelPrime he bound res
  | exp v =>
    let m := multiplicity X y.denom
    have hspec : m ≤ special t.D (.exp v) lower a b d := by
      rcases special_order k t v hd' y.denom_ne_zero y.isCoprime_num_denom.isRelPrime hc.symm he
        with hle | ⟨hb0, A, hA, hlog⟩
      · have hdeg := natDegree_le_of_dvd (pow_multiplicity_dvd X (f d)) hd'
        rw [natDegree_X_pow] at hdeg
        have hfd : (f d).natDegree = d.natDegree := by simp [f, natDegree_map]
        exact le_trans (hle.trans (hdeg.trans_eq hfd)) (le_max_left _ _)
      · have hx : b.coeff 0 ≠ 0 := by simpa [f] using hb0
        rw [special, ite_eq_right hx]
        apply le_trans _ (le_max_right _ _)
        apply lower.exponentBound_spec k t hl v _ hg m
        refine ⟨1, A, Nat.one_pos, hA, ?_⟩
        rw [Nat.cast_one, one_mul, div_eq_iff hA]
        rw [hlog]
        simp [m, sub_eq_neg_add]
    have hn := mul_ne_zero (pow_ne_zero (special t.D (.exp v) lower a b d) (X_ne_zero (R := M k n)))
      (mul_ne_zero hd' (pow_ne_zero bound hb'))
    apply (UniqueFactorizationMonoid.dvd_iff_multiplicity_le y.denom_ne_zero hn).mpr
    intro s hs
    rw [← (FiniteMultiplicity.of_prime_left hs hn).pow_dvd_iff_le_multiplicity]
    by_cases hz : s.coeff 0 = 0
    · have hxs := (prime_X.irreducible.dvd_irreducible_iff_associated hs.irreducible).mp
        (X_dvd_iff.mpr hz)
      rw [multiplicity_eq_of_associated_left hxs]
      exact dvd_mul_of_dvd_left (hxs.symm.pow_pow.dvd.trans (pow_dvd_pow X hspec)) _
    · apply dvd_mul_of_dvd_right
      rcases Extension.Pole.order_or_residue _ hs (t.prime_normal_exp k v hg hs hz) hd'
        y.denom_ne_zero y.isCoprime_num_denom.isRelPrime he with hsle | ⟨hsb,hsr⟩
      · exact dvd_mul_of_dvd_left
          ((FiniteMultiplicity.of_prime_left hs hd').pow_dvd_iff_le_multiplicity.mpr hsle) _
      · exact dvd_mul_of_dvd_right ((pow_dvd_pow_of_dvd hsb _).trans
          (pow_dvd_pow _ (res _ _ hs hsb hsr))) _

end SympyProofs.Calculus.Antiderivative.Solve
