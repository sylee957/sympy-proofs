module

public import SympyProofs.Gosper.Algorithm.Normalization
public import SympyProofs.Gosper.Normalization

@[expose] public section
noncomputable section

namespace Gosper.Algorithm

open Polynomial IsLocalization

variable {K : Type} [Field K] [DecidableEq K]

def NormalForm.Nonzero (s : NormalForm K) : Prop := s.A ≠ 0 ∧ s.B ≠ 0 ∧ s.C ≠ 0

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
theorem normalization_step_spec (P Q : K[X]) (s : NormalForm K) (hs : s.Nonzero)
    (he : P * (s.B * s.C) = Q * (s.A * taylor 1 s.C)) (j : ℕ) :
    let d := gcd s.A (taylor (j : K) s.B)
    let t : NormalForm K := ⟨s.A / d, taylor (-(j : K)) (taylor (j : K) s.B / d),
      s.C * taylor (-1) (Gosper.shiftProduct d j)⟩
    t.Nonzero ∧ P * (t.B * t.C) = Q * (t.A * taylor 1 t.C) ∧
      IsCoprime t.A (taylor (j : K) t.B) ∧
      ∀ k, IsCoprime s.A (taylor (k : K) s.B) → IsCoprime t.A (taylor (k : K) t.B) := by
  let d := gcd s.A (taylor (j : K) s.B)
  let a := s.A / d
  let b := taylor (-(j : K)) (taylor (j : K) s.B / d)
  let T := taylor (-1) (Gosper.shiftProduct d j)
  have hd : d ≠ 0 := gcd_ne_zero_of_left hs.1
  have hB : taylor (j : K) s.B ≠ 0 := (taylor_eq_zero _ _).not.mpr hs.2.1
  have ha : s.A = d * a :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left _ _)).symm
  have hb : s.B = taylor (-(j : K)) d * b := by
    have h := congrArg (taylor (-(j : K)))
      (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right s.A (taylor (j : K) s.B))).symm
    simpa [b, d, taylor_mul, taylor_taylor] using h
  refine ⟨⟨left_div_gcd_ne_zero hs.1,
    (taylor_eq_zero _ _).not.mpr (right_div_gcd_ne_zero hB),
    mul_ne_zero hs.2.2 ((taylor_eq_zero _ _).not.mpr (Gosper.shiftProduct_ne_zero _ hd j))⟩,
    ?_, ?_, ?_⟩
  · have hdj : taylor (-(j : K)) d ≠ 0 := (taylor_eq_zero _ _).not.mpr hd
    have ht : T * d = taylor (-(j : K)) d * taylor 1 T := by
      simpa [T, taylor_taylor, mul_comm] using (Gosper.shiftProduct_identity d j).symm
    rw [ha, hb] at he
    change P * (b * (s.C * T)) = Q * (a * taylor 1 (s.C * T))
    apply mul_left_cancel₀ hdj
    rw [taylor_mul]
    linear_combination T * he + (Q * a * taylor 1 s.C) * ht
  · simpa only [taylor_taylor, add_neg_cancel, taylor_zero] using
      (isCoprime_div_gcd_div_gcd (p := s.A) hB)
  · intro k hk
    have hda : a ∣ s.A := ⟨_, by rw [ha]; ring⟩
    have hdb : b ∣ s.B := ⟨_, by rw [hb]; ring⟩
    exact IsCoprime.mono hda ((taylorAlgHom (k : K)).toRingHom.map_dvd hdb) hk

omit [DecidableEq K] in
/-- Fold form of the inline loop invariant. Each step clears its own shift and
preserves all coprimality established before it. -/
theorem normalization_foldl_spec (P Q : K[X]) (step : NormalForm K → ℕ → NormalForm K)
    (hstep : ∀ s, s.Nonzero → P * (s.B * s.C) = Q * (s.A * taylor 1 s.C) → ∀ j,
      (step s j).Nonzero ∧
        P * ((step s j).B * (step s j).C) = Q * ((step s j).A * taylor 1 (step s j).C) ∧
        IsCoprime (step s j).A (taylor (j : K) (step s j).B) ∧
        ∀ k, IsCoprime s.A (taylor (k : K) s.B) →
          IsCoprime (step s j).A (taylor (k : K) (step s j).B))
    (s : NormalForm K) (roots : List ℕ) (hs : s.Nonzero)
    (he : P * (s.B * s.C) = Q * (s.A * taylor 1 s.C)) :
    let t := roots.foldl step s
    t.Nonzero ∧ P * (t.B * t.C) = Q * (t.A * taylor 1 t.C) ∧
      ∀ j, j ∈ roots ∨ IsCoprime s.A (taylor (j : K) s.B) →
        IsCoprime t.A (taylor (j : K) t.B) := by
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

def NormalForm.Valid (P Q : K[X]) (s : NormalForm K) : Prop :=
  s.Nonzero ∧ Gosper.ShiftCoprime s.A s.B ∧
    P * (s.B * s.C) = Q * (s.A * taylor 1 s.C)

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
theorem gosperNormal_sound (backend : Backend K) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (s : NormalForm K)
    (h : gosperNormal backend P Q = s) :
    s.Nonzero ∧ P * (s.B * s.C) = Q * (s.A * taylor 1 s.C) := by
  let a := monic P
  let b := monic Q
  let z := P.leadingCoeff / Q.leadingCoeff
  have ha : a ≠ 0 := monic_ne_zero P hP
  have hb : b ≠ 0 := monic_ne_zero Q hQ
  have hz : z ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  let roots := backend.nonnegativeIntegerRoots (backend.shiftResultant a b)
  let initial : NormalForm K := ⟨a, b, 1⟩
  let step (s : NormalForm K) (j : ℕ) : NormalForm K :=
    let d := gcd s.A (taylor (j : K) s.B)
    ⟨s.A / d, taylor (-(j : K)) (taylor (j : K) s.B / d),
      s.C * taylor (-1) (Gosper.shiftProduct d j)⟩
  let t := (roots.sort (· ≤ ·)).foldl step initial
  have ht := normalization_foldl_spec a b step (normalization_step_spec a b)
    initial (roots.sort (· ≤ ·)) ⟨ha, hb, one_ne_zero⟩
    (by simp [initial]; ring)
  have hs : s = ⟨Polynomial.C z * t.A, t.B, t.C⟩ := by
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
  change P * (t.B * t.C) = Q * (Polynomial.C z * t.A * taylor 1 t.C)
  calc
    _ = Polynomial.C P.leadingCoeff * (a * (t.B * t.C)) := by
      simpa [a, mul_assoc] using congrArg (fun v => v * (t.B * t.C))
        (leadingCoeff_mul_monic P hP).symm
    _ = Polynomial.C P.leadingCoeff * (b * (t.A * taylor 1 t.C)) := by rw [ht.2.1]
    _ = _ := by
      rw [← hz']
      dsimp [b]
      linear_combination (Polynomial.C z * t.A * taylor 1 t.C) * leadingCoeff_mul_monic Q hQ

/-- Normalization returns the exact
ratio identity and shift-coprimality required by Gosper's theorem. -/
theorem gosperNormal_exists (backend : Backend K) (hbackend : backend.Valid) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ s, gosperNormal backend P Q = s ∧ s.Valid P Q := by
  let a := monic P
  let b := monic Q
  let z := P.leadingCoeff / Q.leadingCoeff
  have ha : a ≠ 0 := monic_ne_zero P hP
  have hb : b ≠ 0 := monic_ne_zero Q hQ
  have hz : z ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  let roots := backend.nonnegativeIntegerRoots (backend.shiftResultant a b)
  let initial : NormalForm K := ⟨a, b, 1⟩
  let step (s : NormalForm K) (j : ℕ) : NormalForm K :=
    let d := gcd s.A (taylor (j : K) s.B)
    ⟨s.A / d, taylor (-(j : K)) (taylor (j : K) s.B / d),
      s.C * taylor (-1) (Gosper.shiftProduct d j)⟩
  let s := (roots.sort (· ≤ ·)).foldl step initial
  have hs := normalization_foldl_spec a b step (normalization_step_spec a b)
    initial (roots.sort (· ≤ ·)) ⟨ha, hb, one_ne_zero⟩
    (by simp [initial]; ring)
  let result : NormalForm K := ⟨Polynomial.C z * s.A, s.B, s.C⟩
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
    (s : NormalForm K) (h : gosperNormal backend P Q = s) : s.Valid P Q := by
  obtain ⟨t, ht, hs⟩ := gosperNormal_exists backend hbackend P Q hP hQ
  have : t = s := ht.symm.trans h
  simpa [this] using hs

end Gosper.Algorithm
