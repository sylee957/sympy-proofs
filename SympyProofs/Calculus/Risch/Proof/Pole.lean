module

public import SympyProofs.Calculus.Risch.Proof.Deriv
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Poles of a solution of `Y′ + (N/B) Y = H/T` at a tower step (Risch 1969, pp. 186–187),
at primes that are normal for the derivation. A pole of the solution deeper than that of the
right-hand side forces a simple pole of the coefficient whose residue is the order of the
pole. At a primitive step every prime is normal. At an exponential step every prime other
than the generator is normal, and at the generator itself a pole of the solution deeper than
that of the right-hand side makes the lowest coefficients cancel: their ratio is then a field
element whose logarithmic derivative is known up to the order of the pole times the
derivative of the exponent. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

namespace Pole

section Abstract

variable {F : Type*} [Field F] [CharZero F]

/-- The differential equation with unknown `u/d`, cleared of denominators. -/
def Equation (δ : Derivation ℤ F[X] F[X]) (N B H T u d : F[X]) : Prop :=
  ((δ u * d - u * δ d) * B + N * u * d) * T = H * d ^ 2 * B

omit [CharZero F] in
/-- The numerator of the derivative of `u / (s ^ (j + 1) * t)` is divisible by `s ^ j`. -/
theorem derivative_at_pole (δ : Derivation ℤ F[X] F[X]) (s u t : F[X]) (j : ℕ) :
    δ u * (s ^ (j+1) * t) - u * δ (s ^ (j+1) * t) =
      s ^ j * ((δ u * t - u * δ t) * s - u * C ((j+1 : ℕ) : F) * δ s * t) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Nat.add_sub_cancel, map_natCast]
  rw [pow_succ]
  push_cast
  ring

/-- At a normal prime where the right-hand side has too small a pole, the coefficient has a
pole and equals the solution's pole order times the logarithmic derivative there. -/
theorem order_or_residue (δ : Derivation ℤ F[X] F[X]) {N B H T u d s : F[X]} (hs : Prime s)
    (normal : ¬ s ∣ δ s) (hT : T ≠ 0) (hd : d ≠ 0) (hu : IsRelPrime u d)
    (he : Equation δ N B H T u d) :
    multiplicity s d ≤ multiplicity s T ∨
      (s ∣ B ∧ s ∣ N - C (multiplicity s d : F) * δ B) := by
  by_cases hle : multiplicity s d ≤ multiplicity s T
  · exact Or.inl hle
  right
  obtain ⟨t, ht, hst⟩ := (FiniteMultiplicity.of_prime_left hs hd).exists_eq_pow_mul_and_not_dvd
  generalize hj : multiplicity s d = j at ht hle ⊢
  cases j with
  | zero => omega
  | succ j =>
    have hsd : s ∣ d := ht ▸ dvd_mul_of_dvd_left (dvd_pow_self s (Nat.succ_ne_zero j)) _
    have hsu : ¬s ∣ u := fun h => hs.not_isUnit (hu h hsd)
    have sc : ¬s ∣ C ((j+1 : ℕ) : F) := fun h => hs.not_isUnit (isUnit_of_dvd_unit h
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)))))
    obtain ⟨a, ha⟩ : ∃ a : F[X], a = (δ u * t - u * δ t) * s - u * C ((j+1 : ℕ) : F) * δ s * t :=
      ⟨_, rfl⟩
    have hna : ¬s ∣ a := by
      intro h
      have e := dvd_sub (dvd_mul_left s (δ u * t - u * δ t)) h
      rw [ha, sub_sub_cancel] at e
      simp only [hs.dvd_mul, hsu, sc, normal, hst, or_self] at e
    obtain ⟨w, hw⟩ : ∃ w : F[X], w = a * B + N * u * s * t := ⟨_, rfl⟩
    have key : w * T = H * s ^ (j+2) * t ^ 2 * B := by
      apply mul_left_cancel₀ (pow_ne_zero j hs.ne_zero)
      unfold Equation at he
      rw [ht, derivative_at_pole, ← ha] at he
      rw [hw]
      simp only [pow_succ] at he ⊢
      linear_combination he
    obtain ⟨v, hv, hsv⟩ := (FiniteMultiplicity.of_prime_left hs hT).exists_eq_pow_mul_and_not_dvd
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = multiplicity s T := ⟨_, rfl⟩
    rw [← hm] at hv hle
    have hmj : m ≤ j := by omega
    have sq : s ^ 2 ∣ w := by
      apply hs.pow_dvd_of_dvd_mul_right _ hsv
      refine ⟨H * s ^ (j-m) * t ^ 2 * B, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero m hs.ne_zero)
      have ar : j + 2 = m + 2 + (j - m) := by omega
      rw [hv, ar, pow_add, pow_add] at key
      linear_combination key
    have first : s ∣ B := by
      have hw' : s ∣ w := (dvd_pow_self s (by decide : 2 ≠ 0)).trans sq
      have hu' : s ∣ N * u * s * t := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      rw [hw] at hw'
      exact (hs.dvd_mul.mp ((dvd_add_left hu').mp hw')).resolve_left hna
    obtain ⟨b, hb⟩ := first
    refine ⟨⟨b, hb⟩, ?_⟩
    have second : s ∣ a * b + N * u * t := by
      obtain ⟨e, he'⟩ := sq
      refine ⟨e, mul_left_cancel₀ hs.ne_zero ?_⟩
      rw [hw, hb] at he'
      linear_combination he'
    have sd : s ∣ u * t * (N - C ((j+1 : ℕ) : F) * δ B) := by
      obtain ⟨e, he'⟩ := second
      refine ⟨e - (δ u * t - u * δ t) * b - u * t * C ((j+1 : ℕ) : F) * δ b, ?_⟩
      rw [hb, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [ha] at he'
      linear_combination he'
    exact (hs.dvd_mul.mp sd).resolve_left (fun h => (hs.dvd_mul.mp h).elim hsu hst)

/-- A uniform bound on integral residues gives one denominator for all solutions. -/
theorem denominator_dvd (δ : Derivation ℤ F[X] F[X]) {N B H T u d : F[X]}
    (normal : ∀ s : F[X], Prime s → ¬ s ∣ δ s) (hB : B ≠ 0) (hT : T ≠ 0) (hd : d ≠ 0)
    (hu : IsRelPrime u d) (he : Equation δ N B H T u d) (bound : ℕ)
    (res : ∀ (s : F[X]) (m : ℕ), Prime s → s ∣ B → s ∣ N - C (m : F) * δ B → m ≤ bound) :
    d ∣ T * B ^ bound := by
  have hn := mul_ne_zero hT (pow_ne_zero bound hB)
  apply (UniqueFactorizationMonoid.dvd_iff_multiplicity_le hd hn).mpr
  intro s hs
  rw [← (FiniteMultiplicity.of_prime_left hs hn).pow_dvd_iff_le_multiplicity]
  rcases order_or_residue δ hs (normal s hs) hT hd hu he with le | ⟨hb, hr⟩
  · exact dvd_mul_of_dvd_left
      ((FiniteMultiplicity.of_prime_left hs hT).pow_dvd_iff_le_multiplicity.mpr le) _
  · apply dvd_mul_of_dvd_right _ T
    exact (pow_dvd_pow_of_dvd hb _).trans (pow_dvd_pow B (res s _ hs hb hr))

end Abstract

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

noncomputable local instance intAlgebraPole {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-- The cleared equation agrees with the tower derivation of rational functions. -/
theorem equation_iff (t : Tower (n+1)) {N B H T u d : (K k n)[X]} (hb : B ≠ 0) (ht : T ≠ 0)
    (hd : d ≠ 0) :
    Equation (Tower.polyDer k t) N B H T u d ↔
      t.der k (ι u / ι d) + (ι N / ι B) * (ι u / ι d) = ι H / ι T := by
  rw [Derivation.leibniz_div, Tower.der_algebraMap, Tower.der_algebraMap]
  simp only [smul_eq_mul]
  have hb' := RatFunc.algebraMap_ne_zero hb
  have ht' := RatFunc.algebraMap_ne_zero ht
  have hd' := RatFunc.algebraMap_ne_zero hd
  constructor
  · intro he
    have he' := congrArg ι he
    simp only [map_mul, map_add, map_sub, map_pow] at he'
    field_simp [hb', ht', hd']
    linear_combination he'
  · intro he
    field_simp [hb', ht', hd'] at he
    apply RatFunc.algebraMap_injective (K k n)
    simp only [map_mul, map_add, map_sub, map_pow]
    linear_combination he

/-- The quotient rule for the tower derivation of a quotient of polynomials. -/
theorem der_div (t : Tower (n+1)) (u : (K k n)[X]) {d : (K k n)[X]} (hd : d ≠ 0) :
    t.der k (ι u / ι d) =
      ι (Tower.polyDer k t u * d - u * Tower.polyDer k t d) / ι (d * d) := by
  have hd' := RatFunc.algebraMap_ne_zero hd
  rw [Derivation.leibniz_div, Tower.der_algebraMap, Tower.der_algebraMap]
  simp only [smul_eq_mul, map_mul, map_sub]
  field_simp [hd']

/-- The coefficients of the derivative of a polynomial in a primitive generator. -/
theorem coeff_polyDer_prim (t : Tower n) (b : Term n) (P : (K k n)[X]) (i : ℕ) :
    (Tower.polyDer k (t.prim b) P).coeff i =
      t.der k (P.coeff i) + ((i+1 : ℕ) : K k n) * Term.value k b * P.coeff (i+1) := by
  let _ : Differential (K k n) := ⟨t.der k⟩
  change (affine 0 (Term.value k b) P).coeff i = _
  rw [coeff_affine]
  simp only [mul_zero, zero_mul, add_zero]
  rfl

/-- The coefficients of the derivative of a polynomial in an exponential generator. -/
theorem coeff_polyDer_exp (t : Tower n) (u : Term n) (P : (K k n)[X]) (i : ℕ) :
    (Tower.polyDer k (t.exp u) P).coeff i =
      t.der k (P.coeff i) + (i : K k n) * t.der k (Term.value k u) * P.coeff i := by
  let _ : Differential (K k n) := ⟨t.der k⟩
  change (affine (t.der k (Term.value k u)) 0 P).coeff i = _
  rw [coeff_affine]
  simp only [mul_zero, zero_mul, add_zero]
  rfl

/-- At an admissible primitive step every prime polynomial is normal. -/
theorem prim_normal {t : Tower n} {b : Term n} (ht : (t.prim b).Admissible k)
    {s : (K k n)[X]} (hs : Prime s) : ¬ s ∣ Tower.polyDer k (t.prim b) s := by
  intro dvd
  have lc : s.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hs.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : (K k n)[X], m = s * C s.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have mon : m.Monic := hm ▸ monic_mul_leadingCoeff_inv hs.ne_zero
  have sm : s = m * C s.leadingCoeff := by
    rw [hm, mul_assoc, ← C_mul, inv_mul_cancel₀ lc, C_1, mul_one]
  have mdvd : m ∣ Tower.polyDer k (t.prim b) m := by
    have h1 : s ∣ Tower.polyDer k (t.prim b) m := by
      rw [hm, Derivation.leibniz]
      exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_left dvd _)
    exact (Dvd.intro _ sm.symm).trans h1
  have deg : m.natDegree = s.natDegree := by
    rw [hm, natDegree_mul_C (inv_ne_zero lc)]
  have pos : 0 < m.natDegree := deg ▸ hs.irreducible.natDegree_pos
  have small : (Tower.polyDer k (t.prim b) m).degree < m.degree := by
    rw [degree_eq_natDegree mon.ne_zero, degree_lt_iff_coeff_zero]
    intro i hi
    have hi' : m.natDegree ≤ i := hi
    rw [coeff_polyDer_prim, coeff_eq_zero_of_natDegree_lt (show m.natDegree < i + 1 by omega)]
    rcases hi'.eq_or_lt with e | lt
    · rw [← e, coeff_natDegree, mon.leadingCoeff]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt lt]
      simp
  have zero : Tower.polyDer k (t.prim b) m = 0 := eq_zero_of_dvd_of_degree_lt mdvd small
  have cf := congrArg (fun p : (K k n)[X] => p.coeff (m.natDegree - 1)) zero
  simp only [coeff_polyDer_prim, Nat.sub_add_cancel pos, coeff_natDegree, mon.leadingCoeff,
    mul_one, coeff_zero] at cf
  apply ht.2.2
  refine ⟨-(m.coeff (m.natDegree - 1)) / (m.natDegree : K k n), ?_⟩
  rw [Derivation.leibniz_div_const _ _ _ (Derivation.map_natCast ..), smul_eq_mul,
    inv_mul_eq_div, map_neg, div_eq_iff (Nat.cast_ne_zero.mpr pos.ne')]
  linear_combination -cf

variable {t : Tower n} {u : Term n}

/-- Two logarithmic derivatives differing by an integral multiple of the derivative of an
admissible exponent agree. -/
theorem multiple_unique
    (hu : ¬ ∃ (m : ℕ) (v : K k n), 0 < m ∧ v ≠ 0 ∧
      t.der k v / v = (m : K k n) * t.der k (Term.value k u))
    {g : K k n} {α β : ℤ} {A B : K k n} (hA : A ≠ 0) (hB : B ≠ 0)
    (eA : t.der k A = (g + (α : K k n) * t.der k (Term.value k u)) * A)
    (eB : t.der k B = (g + (β : K k n) * t.der k (Term.value k u)) * B) : α = β := by
  have ratio (α β : ℤ) (A B : K k n) (hA : A ≠ 0) (hB : B ≠ 0)
      (eA : t.der k A = (g + (α : K k n) * t.der k (Term.value k u)) * A)
      (eB : t.der k B = (g + (β : K k n) * t.der k (Term.value k u)) * B) (lt : β < α) :
      False := by
    apply hu
    refine ⟨(α - β).toNat, A / B, by omega, div_ne_zero hA hB, ?_⟩
    have cast : (((α - β).toNat : ℕ) : K k n) = (α : K k n) - (β : K k n) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_sub]
    rw [cast, Derivation.leibniz_div, eA, eB]
    simp only [smul_eq_mul]
    field_simp
    ring
  rcases lt_trichotomy α β with h | h | h
  · exact (ratio β α B A hB hA eB eA h).elim
  · exact h
  · exact (ratio α β A B hA hB eA eB h).elim

/-- A power of an exponential generator is an eigenvector of the derivation. -/
theorem polyDer_X_pow (t : Tower n) (u : Term n) (a : ℕ) :
    Tower.polyDer k (t.exp u) (X ^ a) = C ((a : K k n) * t.der k (Term.value k u)) * X ^ a := by
  ext i
  rw [coeff_polyDer_exp, coeff_C_mul, coeff_X_pow]
  split
  · rename_i h
    subst h
    simp
  · simp

/-- At an exponential step the constant term of the derivative is the derivative of the
constant term. -/
theorem coeff_zero_polyDer (t : Tower n) (u : Term n) (P : (K k n)[X]) :
    (Tower.polyDer k (t.exp u) P).coeff 0 = t.der k (P.coeff 0) := by
  rw [coeff_polyDer_exp]
  simp

/-- At an admissible exponential step every prime with nonzero constant term is normal. -/
theorem exp_normal (ht : (t.exp u).Admissible k) {s : (K k n)[X]} (hs : Prime s)
    (h0 : s.coeff 0 ≠ 0) : ¬ s ∣ Tower.polyDer k (t.exp u) s := by
  intro dvd
  have lc : s.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hs.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : (K k n)[X], m = s * C s.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have mon : m.Monic := hm ▸ monic_mul_leadingCoeff_inv hs.ne_zero
  have sm : s = m * C s.leadingCoeff := by
    rw [hm, mul_assoc, ← C_mul, inv_mul_cancel₀ lc, C_1, mul_one]
  have mdvd : m ∣ Tower.polyDer k (t.exp u) m := by
    have h1 : s ∣ Tower.polyDer k (t.exp u) m := by
      rw [hm, Derivation.leibniz]
      exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_left dvd _)
    exact (Dvd.intro _ sm.symm).trans h1
  have deg : m.natDegree = s.natDegree := by
    rw [hm, natDegree_mul_C (inv_ne_zero lc)]
  have pos : 0 < m.natDegree := deg ▸ hs.irreducible.natDegree_pos
  have small : (Tower.polyDer k (t.exp u) m -
      C ((m.natDegree : K k n) * t.der k (Term.value k u)) * m).degree < m.degree := by
    rw [degree_eq_natDegree mon.ne_zero, degree_lt_iff_coeff_zero]
    intro i hi
    have hi' : m.natDegree ≤ i := hi
    rw [coeff_sub, coeff_polyDer_exp, coeff_C_mul]
    rcases hi'.eq_or_lt with e | lt
    · rw [← e, coeff_natDegree, mon.leadingCoeff]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt lt]
      simp
  have zero := eq_zero_of_dvd_of_degree_lt (dvd_sub mdvd (dvd_mul_left m _)) small
  have cf := congrArg (fun p : (K k n)[X] => p.coeff 0) zero
  simp only [coeff_sub, coeff_zero_polyDer, coeff_C_mul, coeff_zero] at cf
  have m0 : m.coeff 0 ≠ 0 := by
    rw [hm, coeff_mul_C]
    exact mul_ne_zero h0 (inv_ne_zero lc)
  apply ht.2.2
  refine ⟨m.natDegree, m.coeff 0, pos, m0, (div_eq_iff m0).mpr ?_⟩
  linear_combination cf

/-- At the generator of an exponential step: a pole of the solution deeper than that of the
right-hand side gives a field element with the indicated logarithmic derivative. -/
theorem special_order {N B H T v d : (K k n)[X]} (hT : T ≠ 0) (hd : d ≠ 0)
    (hu : IsRelPrime v d) (cop : IsCoprime N B)
    (he : Equation (Tower.polyDer k (t.exp u)) N B H T v d) :
    multiplicity X d ≤ multiplicity X T ∨ (B.coeff 0 ≠ 0 ∧ ∃ A : K k n, A ≠ 0 ∧
      t.der k A = ((multiplicity X d : K k n) * t.der k (Term.value k u) -
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
  have δd : Tower.polyDer k (t.exp u) d = X ^ (m + j + 1) *
      (C (((m + j + 1 : ℕ) : K k n) * t.der k (Term.value k u)) * d₁ +
        Tower.polyDer k (t.exp u) d₁) := by
    rw [hd₁, Derivation.leibniz, polyDer_X_pow]
    simp only [smul_eq_mul]
    ring
  obtain ⟨W, hW⟩ : ∃ W, W = (Tower.polyDer k (t.exp u) v * d₁ -
      v * (C (((m + j + 1 : ℕ) : K k n) * t.der k (Term.value k u)) * d₁ +
        Tower.polyDer k (t.exp u) d₁)) * B + N * v * d₁ := ⟨_, rfl⟩
  have key : W * T₁ = H * X ^ (j + 1) * d₁ ^ 2 * B := by
    apply mul_left_cancel₀ (pow_ne_zero (m + j + 1 + m) (X_ne_zero (R := K k n)))
    unfold Equation at he
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
  have Xd : (X : (K k n)[X]) ∣ d := by
    rw [hd₁, pow_succ]
    exact ⟨X ^ (m + j) * d₁, by ring⟩
  have v0 : v.coeff 0 ≠ 0 := fun z => not_isUnit_X (hu (X_dvd_iff.mpr z) Xd)
  have d0 : d₁.coeff 0 ≠ 0 := fun z => hXd (X_dvd_iff.mpr z)
  rw [hW] at W0
  simp only [coeff_add, coeff_sub, mul_coeff_zero, coeff_zero_polyDer, coeff_C_zero] at W0
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

/-- The denominator of every solution at an exponential step, given a bound for its order
at the generator. -/
theorem exp_denominator_dvd (ht : (t.exp u).Admissible k) {N B H T v d : (K k n)[X]}
    (hB : B ≠ 0) (hT : T ≠ 0) (hd : d ≠ 0) (hu : IsRelPrime v d)
    (he : Equation (Tower.polyDer k (t.exp u)) N B H T v d) (bound : ℕ)
    (res : ∀ (s : (K k n)[X]) (m : ℕ), Prime s → s ∣ B →
      s ∣ N - C (m : K k n) * Tower.polyDer k (t.exp u) B → m ≤ bound)
    (e : ℕ) (special : multiplicity X d ≤ e) : d ∣ X ^ e * (T * B ^ bound) := by
  have hn : X ^ e * (T * B ^ bound) ≠ 0 :=
    mul_ne_zero (pow_ne_zero e X_ne_zero) (mul_ne_zero hT (pow_ne_zero bound hB))
  apply (UniqueFactorizationMonoid.dvd_iff_multiplicity_le hd hn).mpr
  intro s hs
  rw [← (FiniteMultiplicity.of_prime_left hs hn).pow_dvd_iff_le_multiplicity]
  by_cases hsX : s.coeff 0 = 0
  · have assoc : Associated X s :=
      (prime_X.irreducible.dvd_irreducible_iff_associated hs.irreducible).mp (X_dvd_iff.mpr hsX)
    have eqm : multiplicity s d = multiplicity X d := multiplicity_eq_of_associated_left assoc
    rw [eqm]
    exact dvd_mul_of_dvd_left ((assoc.symm.pow_pow.dvd).trans (pow_dvd_pow X special)) _
  · apply dvd_mul_of_dvd_right
    rcases order_or_residue (Tower.polyDer k (t.exp u)) hs (exp_normal ht hs hsX) hT hd hu he
      with le | ⟨hb, hr⟩
    · exact dvd_mul_of_dvd_left
        ((FiniteMultiplicity.of_prime_left hs hT).pow_dvd_iff_le_multiplicity.mpr le) _
    · apply dvd_mul_of_dvd_right _ T
      exact (pow_dvd_pow_of_dvd hb _).trans (pow_dvd_pow B (res s _ hs hb hr))

end Pole

end SympyProofs.Calculus.Risch
