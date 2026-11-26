module

public import SympyProofs.Calculus.Antiderivative.Proof.ConstantsConverse
public import SympyProofs.Calculus.Antiderivative.Proof.PolynomialDerivation
public import SympyProofs.Calculus.Antiderivative.Proof.Trigonometric.Model

/-! The native tangent derivation has precisely the irreducible factors of
`1 + X²` as special poles. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Tangent

open Polynomial Differential

variable {F : Type} [Field F] [Differential F]

/-- The polynomial derivation for a generator with velocity `v (1 + X²)`. -/
noncomputable abbrev polyDer (v : F) := implicitDeriv (C v * (1 + X^2))

/-- The derivative of the distinguished special polynomial is divisible by it. -/
theorem special (v : F) : (1 + X^2 : F[X]) ∣ polyDer v (1 + X^2) := by
  refine ⟨2 * X * C v,?_⟩
  simp [polyDer,Derivation.leibniz_pow]
  ring

private theorem coeff_succ (v : F) (p : F[X]) (j : ℕ) :
    (polyDer v p).coeff (j+1) = deriv (p.coeff (j+1)) +
      v * (p.coeff (j+2) * (j+2 : ℕ) + p.coeff j * (j : F)) := by
  change (mapCoeffs p + C v * (1+X^2) * p.derivative).coeff (j+1) = _
  rw [mul_assoc,add_mul,one_mul,coeff_add,coeff_mapCoeffs,coeff_C_mul,coeff_add,coeff_derivative]
  cases j with
  | zero => norm_num [coeff_X_pow_mul']
  | succ j =>
    rw [coeff_X_pow_mul _ 2 j,coeff_derivative]
    push_cast
    ring

private theorem eigen_slope (v : F) {p q : F[X]} (hp : p ≠ 0)
    (he : polyDer v p = p*q) :
    q = C ((p.natDegree : F)*v) * X + C (q.coeff 0) := by
  have hd : (polyDer v p).natDegree ≤ p.natDegree+1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [coeff_succ, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < l+1),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < l+2),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < l)]
    simp
  have hq : q.natDegree ≤ 1 := by
    by_cases h : q = 0
    · simp [h]
    · rw [he, natDegree_mul hp h] at hd
      omega
  have lin := eq_X_add_C_of_natDegree_le_one hq
  have hl : q.coeff 1 = (p.natDegree : F)*v := by
    have e := congrArg (fun f : F[X] => f.coeff (p.natDegree+1)) he
    rw [lin,mul_add,← mul_assoc,coeff_add,coeff_mul_X,coeff_mul_C,coeff_mul_C,
      coeff_succ,coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree+1),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree+2)] at e
    simp only [map_zero,zero_mul,zero_add,add_zero,coeff_natDegree] at e
    apply mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hp)
    linear_combination -e
  exact lin.trans (by rw [hl])

private theorem eval_fixed (v x : F) (hx : x^2 = -1) (hc : deriv x = 0) (p : F[X]) :
    (polyDer v p).eval x = deriv (p.eval x) := by
  have hv : deriv x = aeval x (C v * (1+X^2)) := by
    simp [hc,hx]
  simpa only [coe_aeval_eq_eval] using (deriv_aeval_eq_implicitDeriv x _ hv p).symm

/-- If there is no logarithmic derivative equal to any positive multiple of `2 i v`, an
irreducible polynomial divides its derivative exactly when it divides `1 + X²`. -/
theorem irreducible_special_iff [CharZero F] (i v : F) (hi : i^2 = -1) (hc : deriv i = 0)
    (adm : ¬ ∃ (m : ℕ) (y : F), 0 < m ∧ y ≠ 0 ∧ deriv y / y = (m : F)*(2*i*v))
    {p : F[X]} (hp : Irreducible p) :
    p ∣ polyDer v p ↔ p ∣ 1+X^2 := by
  have hfac : (1+X^2 : F[X]) = (X-C i)*(X-C (-i)) := by
    rw [map_neg]
    have h := congrArg (C : F →+* F[X]) hi
    simp only [map_pow,map_neg,map_one] at h
    linear_combination h
  have hneg : (-i)^2 = -1 := by simpa using hi
  have hdneg : deriv (-i) = 0 := by simp [hc]
  rw [hfac,hp.prime.dvd_mul]
  have fac (x : F) : p ∣ X-C x ↔ p.eval x = 0 :=
    (hp.dvd_comm (irreducible_X_sub_C x)).trans dvd_iff_isRoot
  constructor
  · rintro ⟨q,he⟩
    by_contra! h
    have ha (x : F) (hx : x^2 = -1) (hxc : deriv x = 0) :
        deriv (p.eval x) = p.eval x * q.eval x := by
      rw [← eval_fixed v x hx hxc,he,eval_mul]
    have h₁ := fun hz => h.1 ((fac i).mpr hz)
    have h₂ := fun hz => h.2 ((fac (-i)).mpr hz)
    apply adm
    refine ⟨p.natDegree,p.eval i / p.eval (-i),hp.natDegree_pos,div_ne_zero h₁ h₂,?_⟩
    have e₁ := ha i hi hc
    have e₂ := ha (-i) hneg hdneg
    have slope := eigen_slope v hp.ne_zero he
    rw [slope,eval_add,eval_mul,eval_C,eval_X,eval_C] at e₁ e₂
    rw [Derivation.leibniz_div,smul_eq_mul,smul_eq_mul,e₁,e₂]
    field_simp
    ring
  · rintro (h | h)
    · apply h.trans
      rw [dvd_iff_isRoot]
      change (polyDer v p).eval i = 0
      rw [eval_fixed v i hi hc,(fac i).mp h,map_zero]
    · apply h.trans
      rw [dvd_iff_isRoot]
      change (polyDer v p).eval (-i) = 0
      rw [eval_fixed v (-i) hneg hdneg,(fac (-i)).mp h,map_zero]

end SympyProofs.Calculus.Antiderivative.Trigonometric.Tangent

namespace SympyProofs.Calculus.Antiderivative.Tower

open Trigonometric

open Polynomial

variable {R S : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [CommRing S] [IsDomain S] [DecidableEq S] [NormalizedGCDMonoid S] [Div S] {n : ℕ}
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

noncomputable local instance tangentModelIntAlgebra : Algebra ℤ (M k n) := Ring.toIntAlgebra _

omit [CharZero k] in
theorem tangent_special (t : Tower R n) (u : K R n) :
    (1+X^2 : (M k n)[X]) ∣ t.polyDerModel k (.tan u) (1+X^2) := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  exact Tangent.special (val k (t.D u))

variable [Algebra S k] [FaithfulSMul S k] [CharZero S]

/-- In an admissible native tangent step, the special primes are exactly the factors of
the velocity polynomial `1+X²`. -/
theorem tangent_prime_iff (c : K R 0 →+* K S 0)
    (hc : ∀ a, Model.constantHom k (c a) = Model.constantHom k a) (i : K S 0) (hi : i^2 = -1)
    (t : Tower R n) (u : K R n) (ht : (t.step (.tan u)).Admissible k)
    {p : (M k n)[X]} (hp : Irreducible p) :
    p ∣ t.polyDerModel k (.tan u) p ↔ p ∣ 1+X^2 := by
  let _ : Differential (M k n) := ⟨t.modelD k⟩
  let j := Model.constantHom k i
  let I := Model.C k n j
  let e := t.changeModel k j (constant_ne k i hi)
  let T := (t.compile c i).tower
  let u' := (t.compile c i).value u
  let v := val k (t.D u)
  have hI : I^2 = -1 := by
    change (Model.C k n (Model.constantHom k i))^2 = _
    rw [← map_pow,← map_pow,hi,map_neg,map_one,map_neg,map_one]
  have dI : t.modelD k I = 0 := Model.derivation_C k _ _
  apply Tangent.irreducible_special_iff I v hI dI _ hp
  rintro ⟨m,y,hm,hy,heq⟩
  have hT := ((t.step (.tan u)).compile_admissible_iff k c hc i hi).mpr ht
  have H := ((T.admissible_step_iff k (.exp (2*K.ofConst i*u'))).mp hT).2
  apply H
  refine ⟨m,e y,hm,(map_ne_zero_iff e e.injective).mpr hy,?_⟩
  have hu : e (val k u) = val k u' := by
    rw [show e (val k u) = _ from t.changeModel_val k c hc i hi u,t.compileHom_apply]
  have hv : e v = T.modelD k (val k u') := by
    rw [show v = _ from t.val_D k u,t.changeModel_D k c hc i hi (val k u),hu]
  have hvel : val k (T.D (2*K.ofConst i*u')) = 2*I*e v := by
    rw [Tower.val_D,map_mul (val k),map_mul (val k),map_ofNat,
      ← Model.C_constantHom, hv]
    change T.modelD k (2*I*_) = _
    have dc : T.modelD k I = 0 := T.modelD_C k j
    have dtwo : T.modelD k 2 = 0 := (T.modelD k).map_natCast 2
    simp [Derivation.leibniz,smul_eq_mul,dtwo,dc]
  have ey := congrArg e heq
  change e (t.modelD k y / y) = _ at ey
  rw [map_div₀,t.changeModel_D k c hc i hi y,map_mul,map_natCast,map_mul,map_mul,map_ofNat,
    show e I = I from t.changeModel_C k _ _ j] at ey
  rwa [hvel]

end SympyProofs.Calculus.Antiderivative.Tower
