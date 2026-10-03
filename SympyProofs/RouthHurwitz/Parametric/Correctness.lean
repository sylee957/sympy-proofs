import SympyProofs.RouthHurwitz.FractionFree.Stability
import SympyProofs.RouthHurwitz.Parametric.Invariant

/-! Pointwise correctness of the generated polynomial inequalities. -/
namespace RouthHurwitz.Parametric
open Polynomial Exact FractionFree FractionFree.Arithmetic
variable {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A]

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
private theorem initial_extend (p : Polynomial A) (n parity : ℕ) (j : ℕ) :
    Proofs.extend (initial p n parity) j =
      if 2*j+parity ≤ n then p.coeff n * p.coeff (n-(2*j+parity)) else 0 := by
  change (if h : j < n/2+1 then (initial p n parity)[j] else 0) = _
  by_cases hj : j < n/2+1
  · simp only [dif_pos hj, initial, Vector.getElem_ofFn]
  · have hh : ¬ 2*j+parity ≤ n := by omega
    simp only [dif_neg hj, if_neg hh]

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
private theorem initial_minor (p : Polynomial A) (n k : ℕ) :
    Proofs.minor (initial p n 0) (initial p n 1) k =
      hurwitzMinor (C (p.coeff n) * p) n (k+1) := by
  unfold Proofs.minor hurwitzMinor
  congr 2 <;> funext j <;> simp only [initial_extend, coeff_C_mul, Nat.add_zero]

private theorem stable_smul (p : Polynomial ℝ) (c : ℝ) (hc : c ≠ 0) :
    HurwitzStable (C c * p) ↔ HurwitzStable p := by
  simp only [HurwitzStable, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
    mul_eq_zero, Complex.ofRealHom_eq_coe, Complex.ofReal_eq_zero, hc, false_or]

private theorem run_iff_of_leadingCoeff_ne_zero (p : Polynomial A) (f : A →+* ℝ)
    (hl : f p.leadingCoeff ≠ 0) :
    (run p).Holds f ↔ HurwitzStable (p.map f) := by
  have hd : (p.map f).natDegree = p.natDegree := natDegree_map_of_leadingCoeff_ne_zero f hl
  let q := C p.leadingCoeff * p
  have hqd : (q.map f).natDegree = p.natDegree := by
    simpa only [q, Polynomial.map_mul, Polynomial.map_C, natDegree_C_mul hl] using hd
  have hql : 0 < (q.map f).coeff p.natDegree := by
    simp only [q, Polynomial.map_mul, Polynomial.map_C, coeff_C_mul, coeff_map, coeff_natDegree]
    exact mul_self_pos.mpr hl
  rw [← stable_smul (p.map f) (f p.leadingCoeff) hl]
  rw [show C (f p.leadingCoeff) * p.map f = q.map f by simp [q]]
  rw [hurwitzStable_iff_minors _ p.natDegree hqd hql]
  simp only [Result.Holds, Proofs.run_positive_eq, List.mem_cons, forall_eq_or_imp, map_mul]
  have hsquare : 0 < f p.leadingCoeff * f p.leadingCoeff := mul_self_pos.mpr hl
  rw [and_iff_right hsquare]
  by_cases hn : p.natDegree = 0
  · simp [hn]
    intro k hk he; omega
  · rw [if_neg hn]
    rw [Proofs.loop_positive_iff (algebraMap A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A))]
    simp_rw [initial_minor, hurwitzMinor_map]
    constructor
    · intro h k hk hkn
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact h j (by omega)
    · intro h k hk
      exact h (k+1) (by omega) (by omega)

/-- The generated inequalities hold exactly when the leading coefficient survives
specialization and the resulting real polynomial is Hurwitz stable. Under a parameter
assumption implying the leading coefficient is nonzero, this is a stability equivalence. -/
theorem run_correct (p : Polynomial A) (f : A →+* ℝ) :
    (run p).Holds f ↔ f p.leadingCoeff ≠ 0 ∧ HurwitzStable (p.map f) := by
  constructor
  · intro h
    have hl : f p.leadingCoeff ≠ 0 := by
      intro hz
      have hh := h (p.leadingCoeff * p.leadingCoeff) (by simp [Proofs.run_positive_eq])
      simp [map_mul, hz] at hh
    exact ⟨hl, (run_iff_of_leadingCoeff_ne_zero p f hl).mp h⟩
  · rintro ⟨hl, hs⟩
    exact (run_iff_of_leadingCoeff_ne_zero p f hl).mpr hs

end RouthHurwitz.Parametric
