import SympyProofs.RouthHurwitz.Roots.Count

/-! Root counts under reversal. Reversing coefficients replaces nonzero roots
by their reciprocals, which preserves the sign of the real part. -/

namespace Polynomial

open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem rightCount_C (c : ℂ) : rightCount (C c) = 0 := by
  simp [rightCount, regionCount]

@[simp] theorem rightCount_X : rightCount (X : ℂ[X]) = 0 := by
  simp [rightCount, regionCount]

theorem rightCount_mul {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    rightCount (p * q) = rightCount p + rightCount q := by
  classical
  simp [rightCount, regionCount, roots_mul (mul_ne_zero hp hq)]

@[simp] theorem rightCount_X_sub_C (z : ℂ) :
    rightCount (X - C z) = if 0 < z.re then 1 else 0 := by
  classical
  simp only [rightCount, regionCount, roots_X_sub_C, Multiset.filter_singleton]
  split_ifs <;> simp

@[simp] theorem rightCount_X_pow (n : ℕ) : rightCount ((X : ℂ[X]) ^ n) = 0 := by
  induction n with
  | zero => simpa using rightCount_C 1
  | succ n ih => rw [pow_succ, rightCount_mul (pow_ne_zero _ X_ne_zero) X_ne_zero, ih, rightCount_X, add_zero]

theorem reflect_eq_reverse_mul_X_pow (p : ℂ[X]) (n : ℕ) (hn : p.natDegree ≤ n) :
    reflect n p = p.reverse * X ^ (n - p.natDegree) := by
  have h := reflect_mul p (1 : ℂ[X]) (le_refl p.natDegree)
    (show (1 : ℂ[X]).natDegree ≤ n - p.natDegree by simp)
  simpa [Nat.add_sub_of_le hn, reflect_one, reverse] using h

private theorem reverse_linear (z : ℂ) :
    (X - C z).reverse = 1 - C z * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_one_X, reflect_C]
  simp

private theorem rightCount_reverse_linear (z : ℂ) :
    rightCount (X - C z).reverse = rightCount (X - C z) := by
  classical
  rw [reverse_linear]
  by_cases hz : z = 0
  · simp [hz, rightCount, regionCount, Multiset.filter_singleton]
  have he : (1 - C z * X : ℂ[X]) = C (-z) * (X - C z⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hz]
    simp only [C_neg, C_1]
    ring
  rw [he, rightCount_mul (C_ne_zero.mpr (neg_ne_zero.mpr hz)) (X_sub_C_ne_zero _),
    rightCount_C, zero_add, rightCount_X_sub_C, rightCount_X_sub_C]
  have hs : 0 < z⁻¹.re ↔ 0 < z.re := by
    rw [Complex.inv_re]
    exact div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hz)
  simp only [hs]

/-- Coefficient reversal preserves the right-half-plane root count,
including polynomials with a zero root. -/
theorem rightCount_reverse (p : ℂ[X]) : rightCount p.reverse = rightCount p := by
  classical
  have hprod (s : Multiset ℂ) :
      rightCount (s.map (fun z => X - C z)).prod.reverse =
        rightCount (s.map (fun z => X - C z)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp [reverse, rightCount, regionCount]
    | cons z s ih =>
      have hn : (s.map (fun z => X - C z)).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro hf
        obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hf
        exact X_sub_C_ne_zero a ha
      simp only [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
      rw [rightCount_mul (reverse_eq_zero.not.mpr (X_sub_C_ne_zero _))
        (reverse_eq_zero.not.mpr hn), rightCount_mul (X_sub_C_ne_zero _) hn,
        rightCount_reverse_linear, ih]
  by_cases hp : p = 0
  · simp [hp, rightCount, regionCount]
  have hn : (p.roots.map (fun z => X - C z)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hf
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hf
    exact X_sub_C_ne_zero a ha
  have hfac := (IsAlgClosed.splits p).eq_prod_roots
  conv_lhs => rw [hfac]
  conv_rhs => rw [hfac]
  rw [reverse_mul_of_domain, reverse_C,
    rightCount_mul (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) (reverse_eq_zero.not.mpr hn),
    rightCount_mul (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) hn, hprod]

/-- Reversal at any degree bound preserves the right-half-plane count.
Extra zero roots caused by padding do not contribute. -/
theorem rightCount_reflect (p : ℂ[X]) (n : ℕ) (hn : p.natDegree ≤ n) :
    rightCount (reflect n p) = rightCount p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [reflect_eq_reverse_mul_X_pow p n hn,
    rightCount_mul (reverse_eq_zero.not.mpr hp) (pow_ne_zero _ X_ne_zero),
    rightCount_X_pow, add_zero, rightCount_reverse]

private theorem rootMultiplicity_reverse_linear (a z : ℂ) (hz : z ≠ 0) :
    (X - C a).reverse.rootMultiplicity z = (X - C a).rootMultiplicity z⁻¹ := by
  rw [reverse_linear]
  by_cases ha : a = 0
  · subst a
    simp only [map_zero, zero_mul, sub_zero]
    rw [show (1 : ℂ[X]) = C 1 by simp, rootMultiplicity_C]
    exact (rootMultiplicity_eq_zero (by simpa [IsRoot] using inv_ne_zero hz)).symm
  have he : (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha]
    simp only [C_neg, C_1]
    ring
  rw [he, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha))
    (X_sub_C_ne_zero _)), rootMultiplicity_C, zero_add,
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  simp only [inv_eq_iff_eq_inv]

/-- Multiplicities of nonzero roots are preserved by reciprocal reversal. -/
theorem rootMultiplicity_reverse (p : ℂ[X]) (z : ℂ) (hz : z ≠ 0) :
    p.reverse.rootMultiplicity z = p.rootMultiplicity z⁻¹ := by
  classical
  have hprod (s : Multiset ℂ) :
      (s.map (fun a => X - C a)).prod.reverse.rootMultiplicity z =
        (s.map (fun a => X - C a)).prod.rootMultiplicity z⁻¹ := by
    induction s using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      rw [show (1 : ℂ[X]) = C 1 by simp, reverse_C, rootMultiplicity_C, rootMultiplicity_C]
    | cons a s ih =>
      have hn : (s.map (fun a => X - C a)).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro hf
        obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp hf
        exact X_sub_C_ne_zero b hb
      simp only [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
      rw [rootMultiplicity_mul (mul_ne_zero (reverse_eq_zero.not.mpr (X_sub_C_ne_zero _))
        (reverse_eq_zero.not.mpr hn)), rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) hn),
        rootMultiplicity_reverse_linear a z hz, ih]
  by_cases hp : p = 0
  · simp [hp]
  have hn : (p.roots.map (fun a => X - C a)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hf
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hf
    exact X_sub_C_ne_zero a ha
  have hfac := (IsAlgClosed.splits p).eq_prod_roots
  conv_lhs => rw [hfac]
  conv_rhs => rw [hfac]
  rw [reverse_mul_of_domain, reverse_C,
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp))
      (reverse_eq_zero.not.mpr hn)),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) hn), hprod, rootMultiplicity_C, rootMultiplicity_C]

theorem rootMultiplicity_reflect (p : ℂ[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (z : ℂ) (hz : z ≠ 0) : (reflect n p).rootMultiplicity z = p.rootMultiplicity z⁻¹ := by
  by_cases hp : p = 0
  · simp [hp]
  rw [reflect_eq_reverse_mul_X_pow p n hn,
    rootMultiplicity_mul (mul_ne_zero (reverse_eq_zero.not.mpr hp) (pow_ne_zero _ X_ne_zero)),
    rootMultiplicity_eq_zero (show ¬((X : ℂ[X]) ^ (n - p.natDegree)).IsRoot z by
      simpa [IsRoot] using pow_ne_zero (n - p.natDegree) hz), add_zero,
    rootMultiplicity_reverse p z hz]

/-- Reversal degree is controlled by the original multiplicity at zero. -/
theorem natDegree_reflect_of_le (p : ℂ[X]) (hp : p ≠ 0) (n : ℕ) (hn : p.natDegree ≤ n) :
    (reflect n p).natDegree = n - p.rootMultiplicity 0 := by
  rw [reflect_eq_reverse_mul_X_pow p n hn,
    natDegree_mul (reverse_eq_zero.not.mpr hp) (pow_ne_zero _ X_ne_zero),
    reverse_natDegree, natDegree_X_pow, rootMultiplicity_eq_natTrailingDegree']
  have ht := p.natTrailingDegree_le_natDegree
  omega

end Polynomial
