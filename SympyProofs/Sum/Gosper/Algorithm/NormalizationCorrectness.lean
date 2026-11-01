module

public import SympyProofs.Sum.Gosper.Algorithm.Algorithm
public import SympyProofs.Sum.Gosper.Normalization

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [DecidableEq K]

def normalFormNonzero (s : (K[X] × K[X] × K[X])) : Prop := s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0

/-- The inline root test inserts exactly the nonnegative integer root of a linear factor. -/
theorem normalization_root_step [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]
    (factor : K[X] × ℕ) (shifts : Finset ℕ) :
    (if factor.1.natDegree = 1 then
      if h : IsInteger ℤ (-factor.1.coeff 0 / factor.1.coeff 1) then
        let n : ℤ := Encodable.choose h
        if 0 ≤ n then pure (ForInStep.yield (insert n.toNat shifts))
          else pure (ForInStep.yield shifts)
      else pure (ForInStep.yield shifts)
    else pure (ForInStep.yield shifts) : Id (ForInStep (Finset ℕ))) =
      pure (ForInStep.yield ((nonnegativeIntegerRoot factor.1).elim shifts
        (fun n => insert n shifts))) := by
  by_cases hd : factor.1.natDegree = 1
  · simp only [nonnegativeIntegerRoot, linearRoot, hd, ↓reduceIte]
    split_ifs <;> rfl
  · simp [nonnegativeIntegerRoot, linearRoot, hd]

/-- The explicit gcd update in the normalization loop preserves the ratio and
nonzero polynomials, clears the current shift, and preserves earlier coprimality. -/
theorem normalization_step_spec (P Q : K[X]) (s : (K[X] × K[X] × K[X])) (hs : normalFormNonzero s)
    (he : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)) (j : ℕ) :
    let d := gcd s.1 (taylor (j : K) s.2.1)
    let t : (K[X] × K[X] × K[X]) := (s.1 / d, taylor (-(j : K)) (taylor (j : K) s.2.1 / d),
      s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
    normalFormNonzero t ∧ P * (t.2.1 * t.2.2) = Q * (t.1 * taylor 1 t.2.2) ∧
      IsCoprime t.1 (taylor (j : K) t.2.1) ∧
      ∀ k, IsCoprime s.1 (taylor (k : K) s.2.1) → IsCoprime t.1 (taylor (k : K) t.2.1) := by
  let d := gcd s.1 (taylor (j : K) s.2.1)
  let a := s.1 / d
  let b := taylor (-(j : K)) (taylor (j : K) s.2.1 / d)
  let T := taylor (-1) (Gosper.shiftProduct d j)
  have hd : d ≠ 0 := gcd_ne_zero_of_left hs.1
  have hB : taylor (j : K) s.2.1 ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.2.1
  have ha : s.1 = d * a :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left _ _)).symm
  have hb : s.2.1 = taylor (-(j : K)) d * b := by
    have h := congrArg (taylor (-(j : K)))
      (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right s.1 (taylor (j : K) s.2.1))).symm
    simpa [b, d, taylor_mul, taylor_taylor] using h
  refine ⟨⟨left_div_gcd_ne_zero hs.1,
    (taylor_eq_zero _ _).not.mpr (right_div_gcd_ne_zero hB),
    mul_ne_zero hs.2.2 ((taylor_eq_zero _ _).not.mpr (Gosper.shiftProduct_ne_zero _ hd j))⟩,
    ?_, ?_, ?_⟩
  · have hdj : taylor (-(j : K)) d ≠ 0 := (taylor_eq_zero _ _).not.mpr hd
    have ht : T * d = taylor (-(j : K)) d * taylor 1 T := by
      simpa [T, taylor_taylor, mul_comm] using (Gosper.shiftProduct_identity d j).symm
    rw [ha, hb] at he
    change P * (b * (s.2.2 * T)) = Q * (a * taylor 1 (s.2.2 * T))
    apply mul_left_cancel₀ hdj
    rw [taylor_mul]
    linear_combination T * he + (Q * a * taylor 1 s.2.2) * ht
  · simpa only [taylor_taylor, add_neg_cancel, taylor_zero] using
      (isCoprime_div_gcd_div_gcd (p := s.1) hB)
  · intro k hk
    have hda : a ∣ s.1 := ⟨_, by rw [ha]; ring⟩
    have hdb : b ∣ s.2.1 := ⟨_, by rw [hb]; ring⟩
    exact IsCoprime.mono hda ((taylorAlgHom (k : K)).toRingHom.map_dvd hdb) hk

omit [DecidableEq K] in
/-- Fold form of the inline loop invariant. Each step clears its own shift and
preserves all coprimality established before it. -/
theorem normalization_foldl_spec (P Q : K[X]) (step : (K[X] × K[X] × K[X]) → ℕ → (K[X] × K[X] × K[X]))
    (hstep : ∀ s, normalFormNonzero s → P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2) → ∀ j,
      normalFormNonzero (step s j) ∧
        P * ((step s j).2.1 * (step s j).2.2) = Q * ((step s j).1 * taylor 1 (step s j).2.2) ∧
        IsCoprime (step s j).1 (taylor (j : K) (step s j).2.1) ∧
        ∀ k, IsCoprime s.1 (taylor (k : K) s.2.1) →
          IsCoprime (step s j).1 (taylor (k : K) (step s j).2.1))
    (s : (K[X] × K[X] × K[X])) (roots : List ℕ) (hs : normalFormNonzero s)
    (he : P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)) :
    let t := roots.foldl step s
    normalFormNonzero t ∧ P * (t.2.1 * t.2.2) = Q * (t.1 * taylor 1 t.2.2) ∧
      ∀ j, j ∈ roots ∨ IsCoprime s.1 (taylor (j : K) s.2.1) →
        IsCoprime t.1 (taylor (j : K) t.2.1) := by
  induction roots generalizing s with
  | nil => exact ⟨hs, he, fun j hj => hj.resolve_left (List.not_mem_nil)⟩
  | cons j roots ih =>
    have h := hstep s hs he j
    obtain ⟨hn, hr, hc⟩ := ih (step s j) h.1 h.2.1
    refine ⟨hn, hr, ?_⟩
    intro k hk
    apply hc k
    rcases hk with hk | hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inr h.2.2.1
      · exact Or.inl hk
    · exact Or.inr (h.2.2.2 k hk)

def normalFormValid (P Q : K[X]) (s : (K[X] × K[X] × K[X])) : Prop :=
  normalFormNonzero s ∧ Gosper.ShiftCoprime s.1 s.2.1 ∧
    P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2)

omit [DecidableEq K] in
theorem monic_ne_zero (p : K[X]) (hp : p ≠ 0) : monic p ≠ 0 := by
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hp))) hp

omit [DecidableEq K] in
theorem leadingCoeff_mul_monic (p : K[X]) (hp : p ≠ 0) : C p.leadingCoeff * monic p = p := by
  unfold monic
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hp), map_one, one_mul]

variable [CharZero K] [DecidablePred (IsInteger ℤ : K → Prop)]

/-- Normalization preserves the input ratio over a characteristic-zero
coefficient field. Shift-coprimality is only needed for completeness. -/
theorem gosperNormal_sound (backend : Backend K) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (s : (K[X] × K[X] × K[X]))
    (h : gosperNormal backend P Q = s) :
    normalFormNonzero s ∧ P * (s.2.1 * s.2.2) = Q * (s.1 * taylor 1 s.2.2) := by
  let a := monic P
  let b := monic Q
  let z := P.leadingCoeff / Q.leadingCoeff
  have ha : a ≠ 0 := monic_ne_zero P hP
  have hb : b ≠ 0 := monic_ne_zero Q hQ
  have hz : z ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  let roots := backend.nonnegativeIntegerRoots (backend.shiftResultant a b)
  let initial : (K[X] × K[X] × K[X]) := (a, b, 1)
  let step (s : (K[X] × K[X] × K[X])) (j : ℕ) : (K[X] × K[X] × K[X]) :=
    let d := gcd s.1 (taylor (j : K) s.2.1)
    (s.1 / d, taylor (-(j : K)) (taylor (j : K) s.2.1 / d),
      s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
  let t := (roots.sort (· ≤ ·)).foldl step initial
  have ht := normalization_foldl_spec a b step (normalization_step_spec a b)
    initial (roots.sort (· ≤ ·)) ⟨ha, hb, one_ne_zero⟩
    (by simp [initial]; ring)
  have hs : s = (Polynomial.C z * t.1, t.2.1, t.2.2) := by
    simp only [gosperNormal] at h
    conv at h =>
      pattern (forIn _ (∅ : Finset ℕ) _)
      arg 3
      ext factor shifts
      tactic => exact normalization_root_step factor shifts
    simpa [Backend.shiftResultant, Backend.nonnegativeIntegerRoots,
      nonnegativeIntegerRootsFromFactors_foldl,
      a, b, z, roots, t, initial, step] using h.symm
  rw [hs]
  refine ⟨⟨mul_ne_zero (Polynomial.C_ne_zero.mpr hz) ht.1.1,
    ht.1.2.1, ht.1.2.2⟩, ?_⟩
  have hz' : Polynomial.C Q.leadingCoeff * Polynomial.C z = Polynomial.C P.leadingCoeff := by
    rw [← map_mul]
    congr 1
    dsimp [z]
    field_simp [leadingCoeff_ne_zero.mpr hQ]
  change P * (t.2.1 * t.2.2) = Q * (Polynomial.C z * t.1 * taylor 1 t.2.2)
  calc
    _ = Polynomial.C P.leadingCoeff * (a * (t.2.1 * t.2.2)) := by
      simpa [a, mul_assoc] using congrArg (fun v => v * (t.2.1 * t.2.2))
        (leadingCoeff_mul_monic P hP).symm
    _ = Polynomial.C P.leadingCoeff * (b * (t.1 * taylor 1 t.2.2)) := by rw [ht.2.1]
    _ = _ := by
      rw [← hz']
      dsimp [b]
      linear_combination (Polynomial.C z * t.1 * taylor 1 t.2.2) * leadingCoeff_mul_monic Q hQ

/-- Normalization returns the exact
ratio identity and shift-coprimality required by Gosper's theorem. -/
theorem gosperNormal_exists (backend : Backend K) (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ s, gosperNormal backend P Q = s ∧ normalFormValid P Q s := by
  let a := monic P
  let b := monic Q
  let z := P.leadingCoeff / Q.leadingCoeff
  have ha : a ≠ 0 := monic_ne_zero P hP
  have hb : b ≠ 0 := monic_ne_zero Q hQ
  have hz : z ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  let roots := backend.nonnegativeIntegerRoots (backend.shiftResultant a b)
  let initial : (K[X] × K[X] × K[X]) := (a, b, 1)
  let step (s : (K[X] × K[X] × K[X])) (j : ℕ) : (K[X] × K[X] × K[X]) :=
    let d := gcd s.1 (taylor (j : K) s.2.1)
    (s.1 / d, taylor (-(j : K)) (taylor (j : K) s.2.1 / d),
      s.2.2 * taylor (-1) (Gosper.shiftProduct d j))
  let s := (roots.sort (· ≤ ·)).foldl step initial
  have hs := normalization_foldl_spec a b step (normalization_step_spec a b)
    initial (roots.sort (· ≤ ·)) ⟨ha, hb, one_ne_zero⟩
    (by simp [initial]; ring)
  let result : (K[X] × K[X] × K[X]) := (Polynomial.C z * s.1, s.2.1, s.2.2)
  have hr : gosperNormal backend P Q = result := by
    simp only [gosperNormal]
    conv_lhs =>
      pattern (forIn _ (∅ : Finset ℕ) _)
      arg 3
      ext factor shifts
      tactic => exact normalization_root_step factor shifts
    simp [Backend.shiftResultant, Backend.nonnegativeIntegerRoots,
      nonnegativeIntegerRootsFromFactors_foldl,
      result, s, initial, a, b, roots, z, step]
  have hv := gosperNormal_sound backend P Q hP hQ result hr
  refine ⟨result, hr, hv.1, ?_, hv.2⟩
  intro j
  apply (isCoprime_mul_unit_left_left (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hz)) _ _).mpr
  apply hs.2.2 j
  by_cases hj : j ∈ roots.sort (· ≤ ·)
  · exact Or.inl hj
  · right
    by_contra hn
    exact hj ((backend.mem_shifts hbackend a b ha hb j).mpr hn)

theorem gosperNormal_spec (backend : Backend K) (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (s : (K[X] × K[X] × K[X])) (h : gosperNormal backend P Q = s) : normalFormValid P Q s := by
  obtain ⟨t, ht, hs⟩ := gosperNormal_exists backend hbackend P Q hP hQ
  have : t = s := ht.symm.trans h
  simpa [this] using hs

end Gosper.Algorithm
