module

public import SympyProofs.Calculus.Risch.Proof.Analytic
public import SympyProofs.Calculus.Risch.Proof.Extension

/-! Completeness for functions of a complex variable. On every nonempty open set of regular
points, the functions of an admissible tower are algebraically independent over the complex
numbers (`Tower.realize_independent`). So an identity between the functions of terms on such
a set is an identity in the field of the tower, and when `integrate` finds no elementary
integral, no answer written in a tower of exponentials and logarithms above is a function
with the integrand as its derivative (`integrate_no_function`).

The independence is proved one generator at a time. A polynomial relation of least degree in
the newest generator is differentiated, and the difference with a multiple of itself has
smaller degree, so it vanishes. Its coefficients then give a primitive, or a logarithmic
derivative, that an admissible tower does not have. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Filter Topology

variable {n : ℕ}

/-- The element has a value at every point of `S`. -/
def HasValuesOn (S : Set (Fin n → ℂ)) (x : K ℂ n) : Prop := ∃ y, SpecializesOn S x y

namespace HasValuesOn

variable {S : Set (Fin n → ℂ)} {x x' : K ℂ n}

theorem add (h : HasValuesOn S x) (h' : HasValuesOn S x') : HasValuesOn S (x + x') := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨y', hy'⟩ := h'
  exact ⟨_, hy.add hy'⟩

theorem sub (h : HasValuesOn S x) (h' : HasValuesOn S x') : HasValuesOn S (x - x') := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨y', hy'⟩ := h'
  exact ⟨_, hy.sub hy'⟩

theorem mul (h : HasValuesOn S x) (h' : HasValuesOn S x') : HasValuesOn S (x * x') := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨y', hy'⟩ := h'
  exact ⟨_, hy.mul hy'⟩

theorem natCast (m : ℕ) : HasValuesOn S ((m : ℕ) : K ℂ n) := ⟨_, SpecializesOn.natCast m⟩

theorem zero : HasValuesOn S (0 : K ℂ n) := ⟨_, SpecializesOn.zero⟩

end HasValuesOn

/-- The derivative of a polynomial in the generators has values wherever the tower is
defined, and they are the derivative of the function of the polynomial. -/
theorem SpecializesOn.der_poly (t : Tower n) {S : Set (Fin n → ℂ)}
    (hS : ∀ p ∈ S, ∀ i, (t.vel i).Defined p) (P : MvPolynomial (Fin n) ℂ) :
    ∃ y' : (Fin n → ℂ) → ℂ, SpecializesOn S (t.der ℂ (polyHom ℂ n P)) y' ∧
      ∀ (g : ℂ → Fin n → ℂ) (z : ℂ),
        (∀ i, HasDerivAt (fun w => g w i) ((t.vel i).eval (g z)) z) →
        HasDerivAt (fun w => MvPolynomial.eval (g w) P) (y' (g z)) z := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨fun _ => 0, ?_, fun g z _ => ?_⟩
    · rw [polyHom_C, Tower.der_constHom]
      exact SpecializesOn.zero
    · simpa using hasDerivAt_const z c
  | add P Q hP hQ =>
    obtain ⟨y1, s1, d1⟩ := hP
    obtain ⟨y2, s2, d2⟩ := hQ
    refine ⟨fun p => y1 p + y2 p, ?_, fun g z hg => ?_⟩
    · rw [map_add, map_add]
      exact s1.add s2
    · simp only [map_add]
      exact (d1 g z hg).add (d2 g z hg)
  | mul_X P i hP =>
    obtain ⟨y1, s1, d1⟩ := hP
    refine ⟨fun p => y1 p * p i + MvPolynomial.eval p P * (t.vel i).eval p, ?_,
      fun g z hg => ?_⟩
    · rw [map_mul, polyHom_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, t.der_gens]
      exact (((SpecializesOn.poly P).mul (SpecializesOn.value _ fun p hp => hS p hp i)).add
        ((SpecializesOn.gen i).mul s1)).congr fun p _ => by ring
    · simp only [map_mul, MvPolynomial.eval_X]
      exact (d1 g z hg).mul (hg i)

/-- **The chain rule for elements of the field.** If `x` has the values `y` on `S`, where
the tower is defined, then its derivative has values on `S`, and they are the derivative of
the function `y` along any functions that satisfy the differential equations of the tower
and stay in `S`. -/
theorem SpecializesOn.der (t : Tower n) {S : Set (Fin n → ℂ)}
    (hS : ∀ p ∈ S, ∀ i, (t.vel i).Defined p) {x : K ℂ n} {y : (Fin n → ℂ) → ℂ}
    (h : SpecializesOn S x y) :
    ∃ y' : (Fin n → ℂ) → ℂ, SpecializesOn S (t.der ℂ x) y' ∧
      ∀ (g : ℂ → Fin n → ℂ) (z : ℂ),
        (∀ i, HasDerivAt (fun w => g w i) ((t.vel i).eval (g z)) z) →
        (∀ᶠ w in 𝓝 z, g w ∈ S) → HasDerivAt (fun w => y (g w)) (y' (g z)) z := by
  obtain ⟨P, Q, hx, hPQ⟩ := h
  by_cases hQ : polyHom ℂ n Q = 0
  · -- then `S` is empty
    have empty : ∀ p ∈ S, False := fun p hp => (hPQ p hp).1 (by
      rw [polyHom_injective n (hQ.trans (map_zero _).symm), map_zero])
    exact ⟨fun _ => 0, ⟨0, 0, by simp, fun p hp => (empty p hp).elim⟩,
      fun g z _ ev => (empty _ ev.self_of_nhds).elim⟩
  · have hx' : x = polyHom ℂ n P / polyHom ℂ n Q := by
      rw [eq_div_iff hQ]
      exact hx
    obtain ⟨yP, sP, dP⟩ := SpecializesOn.der_poly t hS P
    obtain ⟨yQ, sQ, dQ⟩ := SpecializesOn.der_poly t hS Q
    refine ⟨fun p => (yP p * MvPolynomial.eval p Q - MvPolynomial.eval p P * yQ p) /
      MvPolynomial.eval p Q ^ 2, ?_, fun g z hg ev => ?_⟩
    · have e : t.der ℂ x = (polyHom ℂ n Q * t.der ℂ (polyHom ℂ n P) -
          polyHom ℂ n P * t.der ℂ (polyHom ℂ n Q)) / polyHom ℂ n Q ^ 2 := by
        rw [hx', Derivation.leibniz_div]
        simp only [smul_eq_mul]
        ring
      rw [e]
      exact ((((SpecializesOn.poly Q).mul sP).sub ((SpecializesOn.poly P).mul sQ)).div
        ((SpecializesOn.poly Q).pow 2) fun p hp => pow_ne_zero 2 (hPQ p hp).1).congr
        fun p _ => by ring
    · have q0 := (hPQ _ ev.self_of_nhds).1
      refine ((dP g z hg).div (dQ g z hg) q0).congr_of_eventuallyEq (ev.mono fun w hw => ?_)
      obtain ⟨qw, e⟩ := hPQ _ hw
      change y (g w) = MvPolynomial.eval (g w) P / MvPolynomial.eval (g w) Q
      rw [eq_div_iff qw]
      exact e

section Step

open Polynomial

local notation "alg" => algebraMap (Polynomial (K ℂ n)) (RatFunc (K ℂ n))

/-- **One generator.** Let `T` adjoin to `t` a generator `θ` with `θ′ = a θ + b`, and let `V`
be an open set of regular points on which the functions of `t` satisfy no polynomial
relation. A polynomial in `θ` over the field of `t`, with coefficients that have values on
`V`, whose function vanishes on `V`, is zero, provided a relation of positive degree `e`
with `l P′ = (l′ + e a l) P`, `l` its leading coefficient, is impossible (`final`). -/
theorem no_relation_step {t : Tower n} {T : Tower (n + 1)} {a b : K ℂ n} {V : Set ℂ}
    (hV : IsOpen V) (cast : ∀ z i, T.realize z i.castSucc = t.realize z i)
    (regT : ∀ z ∈ V, T.RegularAt z) (regt : ∀ z ∈ V, t.RegularAt z)
    (hT : ∀ P : (K ℂ n)[X], ∃ P' : (K ℂ n)[X], T.der ℂ (alg P) = alg P' ∧
      ∀ i, P'.coeff i = t.der ℂ (P.coeff i) + (i : K ℂ n) * a * P.coeff i +
        ((i + 1 : ℕ) : K ℂ n) * b * P.coeff (i + 1))
    (ha : HasValuesOn (t.realize '' V) a) (hb : HasValuesOn (t.realize '' V) b)
    (inj : ∀ x : K ℂ n, SpecializesOn (t.realize '' V) x (fun _ => 0) → x = 0)
    (final : ∀ P : (K ℂ n)[X], 0 < P.natDegree →
      (∀ i, HasValuesOn (t.realize '' V) (P.coeff i)) →
      SpecializesOn (T.realize '' V) (alg P) (fun _ => 0) →
      (∀ x : K ℂ n, HasValuesOn (t.realize '' V) x →
        SpecializesOn (T.realize '' V) (RatFunc.C x : RatFunc (K ℂ n)) (fun _ => 0) → x = 0) →
      (∀ i, P.leadingCoeff * (t.der ℂ (P.coeff i) + (i : K ℂ n) * a * P.coeff i +
          ((i + 1 : ℕ) : K ℂ n) * b * P.coeff (i + 1)) =
        (t.der ℂ P.leadingCoeff + (P.natDegree : K ℂ n) * a * P.leadingCoeff) * P.coeff i) →
      False) :
    ∀ (d : ℕ) (P : (K ℂ n)[X]), P.natDegree ≤ d →
      (∀ i, HasValuesOn (t.realize '' V) (P.coeff i)) →
      SpecializesOn (T.realize '' V) (alg P) (fun _ => 0) → P = 0 := by
  have sub : T.realize '' V ⊆
      {p : Fin (n + 1) → ℂ | (fun i => p i.castSucc) ∈ t.realize '' V} := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, funext fun i => (cast z i).symm⟩
  have liftC {x : K ℂ n} {y : (Fin n → ℂ) → ℂ} (h : SpecializesOn (t.realize '' V) x y) :
      SpecializesOn (T.realize '' V) (RatFunc.C x : RatFunc (K ℂ n))
        fun p => y fun i => p i.castSucc := h.lift.mono sub
  have defT : ∀ p ∈ T.realize '' V, ∀ i, (T.vel i).Defined p := by
    rintro _ ⟨z, hz, rfl⟩
    exact (T.realize_spec z (regT z hz)).1
  have deft : ∀ p ∈ t.realize '' V, ∀ i, (t.vel i).Defined p := by
    rintro _ ⟨z, hz, rfl⟩
    exact (t.realize_spec z (regt z hz)).1
  -- the derivative of an element whose function vanishes on `V` has a function that vanishes
  have derZero {x : K ℂ (n + 1)} (h : SpecializesOn (T.realize '' V) x fun _ => 0) :
      SpecializesOn (T.realize '' V) (T.der ℂ x) fun _ => 0 := by
    obtain ⟨y', s', d'⟩ := SpecializesOn.der T defT h
    refine s'.congr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact (d' T.realize z (T.realize_spec z (regT z hz)).2
      ((hV.eventually_mem hz).mono fun w hw => ⟨w, hw, rfl⟩)).unique (hasDerivAt_const z 0)
  have valDer {x : K ℂ n} (h : HasValuesOn (t.realize '' V) x) :
      HasValuesOn (t.realize '' V) (t.der ℂ x) := by
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', s', -⟩ := SpecializesOn.der t deft hy
    exact ⟨y', s'⟩
  -- an element of the field below whose function vanishes on `V` is zero
  have zeroBelow (x : K ℂ n) (hx : HasValuesOn (t.realize '' V) x)
      (h0 : SpecializesOn (T.realize '' V) (RatFunc.C x : RatFunc (K ℂ n)) fun _ => 0) :
      x = 0 := by
    obtain ⟨y, hy⟩ := hx
    refine inj x (hy.congr ?_)
    rintro _ ⟨z, hz, rfl⟩
    have := (liftC hy).unique h0 (Set.mem_image_of_mem _ hz)
    rwa [show (fun i => T.realize z i.castSucc) = t.realize z from funext (cast z)] at this
  have deg0 (P : (K ℂ n)[X]) (hd : P.natDegree = 0)
      (hc : ∀ i, HasValuesOn (t.realize '' V) (P.coeff i))
      (h0 : SpecializesOn (T.realize '' V) (alg P) fun _ => 0) : P = 0 := by
    have e := eq_C_of_natDegree_eq_zero hd
    rw [e, RatFunc.algebraMap_C] at h0
    rw [e, zeroBelow _ (hc 0) h0, map_zero]
  -- a relation of positive degree gives one of smaller degree
  have step (P : (K ℂ n)[X]) (hP : 0 < P.natDegree)
      (hc : ∀ i, HasValuesOn (t.realize '' V) (P.coeff i))
      (h0 : SpecializesOn (T.realize '' V) (alg P) fun _ => 0) :
      ∃ Q : (K ℂ n)[X], (∀ i, HasValuesOn (t.realize '' V) (Q.coeff i)) ∧
        SpecializesOn (T.realize '' V) (alg Q) (fun _ => 0) ∧
        Q.natDegree ≤ P.natDegree - 1 ∧
        (Q = 0 → ∀ i, P.leadingCoeff * (t.der ℂ (P.coeff i) + (i : K ℂ n) * a * P.coeff i +
            ((i + 1 : ℕ) : K ℂ n) * b * P.coeff (i + 1)) =
          (t.der ℂ P.leadingCoeff + (P.natDegree : K ℂ n) * a * P.leadingCoeff) *
            P.coeff i) := by
    obtain ⟨P', hP', cP'⟩ := hT P
    obtain ⟨c, hc'⟩ : ∃ c, c = t.der ℂ P.leadingCoeff +
        (P.natDegree : K ℂ n) * a * P.leadingCoeff := ⟨_, rfl⟩
    have hlv : HasValuesOn (t.realize '' V) P.leadingCoeff := hc P.natDegree
    have hcv : HasValuesOn (t.realize '' V) c := by
      rw [hc']
      exact (valDer hlv).add (((HasValuesOn.natCast _).mul ha).mul hlv)
    have hP'v : ∀ i, HasValuesOn (t.realize '' V) (P'.coeff i) := fun i => by
      rw [cP']
      exact ((valDer (hc i)).add (((HasValuesOn.natCast i).mul ha).mul (hc i))).add
        (((HasValuesOn.natCast (i + 1)).mul hb).mul (hc (i + 1)))
    refine ⟨C P.leadingCoeff * P' - C c * P, fun i => ?_, ?_, ?_, fun hQ i => ?_⟩
    · rw [coeff_sub, coeff_C_mul, coeff_C_mul]
      exact (hlv.mul (hP'v i)).sub (hcv.mul (hc i))
    · obtain ⟨yl, sl⟩ := hlv
      obtain ⟨yc, sc⟩ := hcv
      have e : alg (C P.leadingCoeff * P' - C c * P) =
          RatFunc.C P.leadingCoeff * T.der ℂ (alg P) - RatFunc.C c * alg P := by
        rw [map_sub, map_mul, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, hP']
      rw [e]
      exact (((liftC sl).mul (derZero h0)).sub ((liftC sc).mul h0)).congr fun p _ => by simp
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hN' : P.natDegree ≤ N := by omega
      rw [coeff_sub, coeff_C_mul, coeff_C_mul, cP', hc']
      rcases hN'.eq_or_lt with rfl | lt
      · rw [coeff_natDegree, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]
        ring
      · rw [coeff_eq_zero_of_natDegree_lt lt,
          coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < N + 1)]
        simp
    · have := congrArg (fun R : (K ℂ n)[X] => R.coeff i) hQ
      simp only [coeff_sub, coeff_C_mul, coeff_zero] at this
      rw [cP', hc'] at this
      exact sub_eq_zero.mp this
  intro d
  induction d with
  | zero =>
    intro P hd hc h0
    exact deg0 P (Nat.le_zero.mp hd) hc h0
  | succ d ih =>
    intro P hd hc h0
    by_contra hP
    rcases Nat.eq_zero_or_pos P.natDegree with e0 | pos
    · exact hP (deg0 P e0 hc h0)
    · obtain ⟨Q, hQc, hQ0, hQd, hQid⟩ := step P pos hc h0
      exact final P pos hc h0 zeroBelow (hQid (ih Q (by omega) hQc hQ0))

/-- The derivation of `T` on polynomials in its newest generator `θ`, where `θ′ = a θ + b`. -/
def StepDer (t : Tower n) (T : Tower (n + 1)) (a b : K ℂ n) : Prop :=
  ∀ P : (K ℂ n)[X], ∃ P' : (K ℂ n)[X], T.der ℂ (alg P) = alg P' ∧
    ∀ i, P'.coeff i = t.der ℂ (P.coeff i) + (i : K ℂ n) * a * P.coeff i +
      ((i + 1 : ℕ) : K ℂ n) * b * P.coeff (i + 1)

/-- No polynomial `P` of positive degree `e` in the newest generator, whose function vanishes
on `V`, satisfies `l P′ = (l′ + e a l) P` with `l` its leading coefficient. -/
def NoRelation (t : Tower n) (T : Tower (n + 1)) (a b : K ℂ n) (V : Set ℂ) : Prop :=
  ∀ P : (K ℂ n)[X], 0 < P.natDegree →
    (∀ i, HasValuesOn (t.realize '' V) (P.coeff i)) →
    SpecializesOn (T.realize '' V) (alg P) (fun _ => 0) →
    (∀ x : K ℂ n, HasValuesOn (t.realize '' V) x →
      SpecializesOn (T.realize '' V) (RatFunc.C x : RatFunc (K ℂ n)) (fun _ => 0) → x = 0) →
    (∀ i, P.leadingCoeff * (t.der ℂ (P.coeff i) + (i : K ℂ n) * a * P.coeff i +
        ((i + 1 : ℕ) : K ℂ n) * b * P.coeff (i + 1)) =
      (t.der ℂ P.leadingCoeff + (P.natDegree : K ℂ n) * a * P.leadingCoeff) * P.coeff i) →
    False

/-- Independence of the functions of `t` on `V` passes to `T`. -/
theorem independent_step {t : Tower n} {T : Tower (n + 1)} {a b : K ℂ n} {V : Set ℂ}
    (hV : IsOpen V) (ne : V.Nonempty) (cast : ∀ z i, T.realize z i.castSucc = t.realize z i)
    (regT : ∀ z ∈ V, T.RegularAt z) (regt : ∀ z ∈ V, t.RegularAt z) (hT : StepDer t T a b)
    (ha : HasValuesOn (t.realize '' V) a) (hb : HasValuesOn (t.realize '' V) b)
    (ih : ∀ P : MvPolynomial (Fin n) ℂ,
      (∀ z ∈ V, MvPolynomial.eval (t.realize z) P = 0) → P = 0)
    (final : NoRelation t T a b V) :
    ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      (∀ z ∈ V, MvPolynomial.eval (T.realize z) P = 0) → P = 0 := by
  intro P hP
  have inj : ∀ x : K ℂ n, SpecializesOn (t.realize '' V) x (fun _ => 0) → x = 0 := fun x hx =>
    hx.eq_zero_of_forall (ne.image _) fun R hR => ih R fun z hz => hR _ ⟨z, hz, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (MvPolynomial (Fin n) ℂ)[X], R = (MvPolynomial.finSuccEquiv ℂ n).toRingHom
      ((MvPolynomial.renameEquiv ℂ (finRotate (n + 1))).toRingHom P) := ⟨_, rfl⟩
  have e : polyHom ℂ (n + 1) P = alg (R.map (polyHom ℂ n)) := by
    rw [polyHom_succ, hR]
    rfl
  have z : R.map (polyHom ℂ n) = 0 :=
    no_relation_step hV cast regT regt hT ha hb inj final _ _ le_rfl
      (fun i => by
        rw [coeff_map]
        exact ⟨_, SpecializesOn.poly _⟩)
      (by
        rw [← e]
        refine (SpecializesOn.poly P).congr ?_
        rintro _ ⟨z, hz, rfl⟩
        exact hP z hz)
  exact polyHom_injective (n + 1) (by rw [e, z, map_zero, map_zero])

/-- A primitive without a primitive in the field below satisfies no relation. -/
theorem noRelation_prim {t : Tower n} {b : Term n} {V : Set ℂ}
    (np : ¬ ∃ v : K ℂ n, t.der ℂ v = Term.value ℂ b) :
    NoRelation t (t.prim b) 0 (Term.value ℂ b) V := by
  intro P pos hc h0 zb ids
  have l0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun z => by
    rw [z, natDegree_zero] at pos
    exact lt_irrefl _ pos
  have e0 : ((P.natDegree : ℕ) : K ℂ n) ≠ 0 := Nat.cast_ne_zero.mpr pos.ne'
  have id := ids (P.natDegree - 1)
  rw [Nat.sub_add_cancel pos, coeff_natDegree] at id
  apply np
  refine ⟨-(P.coeff (P.natDegree - 1) / P.leadingCoeff) / (P.natDegree : K ℂ n), ?_⟩
  have h1 : t.der ℂ (P.coeff (P.natDegree - 1) / P.leadingCoeff) =
      -((P.natDegree : K ℂ n) * Term.value ℂ b) := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    linear_combination id
  rw [Derivation.leibniz_div, map_neg, h1, Derivation.map_natCast]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- An exponential none of whose positive powers lies in the field below, up to a constant,
satisfies no relation. -/
theorem noRelation_exp {t : Tower n} {u : Term n} {V : Set ℂ}
    (np : ¬ ∃ (m : ℕ) (v : K ℂ n), 0 < m ∧ v ≠ 0 ∧
      t.der ℂ v / v = (m : K ℂ n) * t.der ℂ (Term.value ℂ u)) :
    NoRelation t (t.exp u) (t.der ℂ (Term.value ℂ u)) 0 V := by
  intro P pos hc h0 zb ids
  have l0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun z => by
    rw [z, natDegree_zero] at pos
    exact lt_irrefl _ pos
  by_cases hex : ∃ i, i < P.natDegree ∧ P.coeff i ≠ 0
  · obtain ⟨i, hi, pi0⟩ := hex
    refine np ⟨P.natDegree - i, P.coeff i / P.leadingCoeff, by omega, div_ne_zero pi0 l0, ?_⟩
    have id := ids i
    rw [Nat.cast_sub hi.le, Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    linear_combination id
  · push Not at hex
    have eP : P = C P.leadingCoeff * X ^ P.natDegree := by
      ext i
      rw [coeff_C_mul, coeff_X_pow]
      rcases lt_trichotomy i P.natDegree with h | h | h
      · rw [hex i h, ite_eq_right h.ne, mul_zero]
      · rw [h, coeff_natDegree, ite_eq_left rfl, mul_one]
      · rw [coeff_eq_zero_of_natDegree_lt h, ite_eq_right h.ne', mul_zero]
    have hX : SpecializesOn ((t.exp u).realize '' V) (RatFunc.X : RatFunc (K ℂ n))
        fun p => p (Fin.last n) := by
      simpa [gens] using SpecializesOn.gen (S := (t.exp u).realize '' V) (Fin.last n)
    have hl : alg P = RatFunc.C P.leadingCoeff * RatFunc.X ^ P.natDegree := by
      conv_lhs => rw [eP]
      rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [hl] at h0
    have q := h0.div (hX.pow P.natDegree) (by
      rintro _ ⟨z, hz, rfl⟩
      simp [Tower.realize])
    rw [mul_div_assoc, div_self (pow_ne_zero _ RatFunc.X_ne_zero), mul_one] at q
    refine l0 (zb _ (by simpa using hc P.natDegree) (q.congr fun p _ => by simp))

/-- **The functions of an admissible tower are algebraically independent.** A polynomial
that vanishes on the functions of the tower throughout a nonempty open set of regular points
is zero. -/
theorem Tower.realize_independent (t : Tower n) (adm : t.Admissible ℂ) {V : Set ℂ}
    (hV : IsOpen V) (ne : V.Nonempty) (reg : ∀ z ∈ V, t.RegularAt z) :
    ∀ P : MvPolynomial (Fin n) ℂ,
      (∀ z ∈ V, MvPolynomial.eval (t.realize z) P = 0) → P = 0 := by
  induction t with
  | const =>
    intro P hP
    obtain ⟨z, hz⟩ := ne
    have h := hP z hz
    rw [MvPolynomial.eq_C_of_isEmpty P] at h ⊢
    rw [MvPolynomial.eval_C] at h
    rw [h, map_zero]
  | @prim n t b ih =>
    obtain ⟨at', -, np⟩ := adm
    have regt : ∀ z ∈ V, t.RegularAt z := fun z hz => (reg z hz).1
    refine independent_step hV ne (fun z i => by simp [Tower.realize]) reg regt ?_
      HasValuesOn.zero ⟨_, SpecializesOn.value b ?_⟩ (ih at' regt) (noRelation_prim np)
    · intro P
      let : Differential (K ℂ n) := ⟨t.der ℂ⟩
      exact ⟨affine 0 (Term.value ℂ b) P, extend_poly _ P, fun i => coeff_affine 0 _ P i⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (reg z hz).2.1
  | @exp n t u ih =>
    obtain ⟨at', -, np⟩ := adm
    have regt : ∀ z ∈ V, t.RegularAt z := fun z hz => (reg z hz).1
    refine independent_step hV ne (fun z i => by simp [Tower.realize]) reg regt ?_
      ⟨fun p => (t.D u).eval p, ?_⟩ HasValuesOn.zero (ih at' regt) (noRelation_exp np)
    · intro P
      let : Differential (K ℂ n) := ⟨t.der ℂ⟩
      exact ⟨affine (t.der ℂ (Term.value ℂ u)) 0 P, extend_poly _ P,
        fun i => coeff_affine _ 0 P i⟩
    · rw [Tower.der_value]
      refine SpecializesOn.value (t.D u) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact Term.defined_deriv (t.realize_spec z (regt z hz)).1 u (reg z hz).2

end Step

/-- **Completeness for functions of a complex variable.** When `integrate` returns
`nonelementary`, no answer written in a tower obtained from `t` by adjoining exponentials
and logarithms, and accepted by `admissible`, is a function with the integrand as its
derivative: not on any nonempty open set where the larger tower, the integrand and the
answer are regular. The generators are read as the variable, exponentials and principal
logarithms (`Tower.realize`), and so is the answer (`Answer.realize`). -/
theorem integrate_no_function {t : Tower n} {f : Term n} (hf : f.defined = true)
    (h : integrate t f = .nonelementary) {d : ℕ} {t' : Tower (n + d)}
    (ext : t.ElementaryExt d t') (ht' : admissible t' = true) (a : Answer (n + d))
    {V : Set ℂ} (hV : IsOpen V) (ne : V.Nonempty)
    (reg : ∀ z ∈ V, t'.RegularAt z ∧ (f.lift d).Defined (t'.realize z) ∧
      a.RegularAt (t'.realize z)) :
    ¬ ∀ z ∈ V, HasDerivAt (fun w => a.realize (t'.realize w))
      ((f.lift d).eval (t'.realize z)) z := by
  intro hd
  refine integrate_no_answer (k := ℂ) hf h ext ht' a (sub_eq_zero.mp ?_)
  have left : SpecializesOn (t'.realize '' V) (Term.value ℂ (f.lift d))
      fun p => (f.lift d).eval p := SpecializesOn.value _ (by
    rintro _ ⟨z, hz, rfl⟩
    exact (reg z hz).2.1)
  have right : SpecializesOn (t'.realize '' V) (a.deriv ℂ t') (a.derivAt t') :=
    a.specializesOn_deriv (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨(t'.realize_spec z (reg z hz).1).1, (reg z hz).2.2⟩)
  refine SpecializesOn.eq_zero_of_forall ((right.sub left).congr ?_) (ne.image _) fun P hP =>
    t'.realize_independent (admissible_sound ht') hV ne (fun z hz => (reg z hz).1) P
      fun z hz => hP _ ⟨z, hz, rfl⟩
  rintro _ ⟨z, hz, rfl⟩
  have d1 := a.hasDerivAt_realize_derivAt (t := t') (t'.realize_spec z (reg z hz).1).2
    (reg z hz).2.2
  rw [d1.unique (hd z hz)]
  exact sub_self _

end SympyProofs.Calculus.Risch
