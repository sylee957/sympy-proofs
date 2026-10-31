module

public import SympyProofs.Gosper.RationalSum.Preparation

/-! Loop invariants for extracting the powers of one shifted denominator factor. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
variable {K : Type*} [Field K] [Algebra ℚ K]

def certificateDifference (c : Array (ShiftSum K)) : RatFunc K :=
  (c.map fun s => s.expandAt 1 - s.expandAt 0).sum

theorem certificateDifference_push (c : Array (ShiftSum K)) (s : ShiftSum K) :
    certificateDifference (c.push s) = certificateDifference c +
      (s.fractionAt (s.length : K) - s.fractionAt 0) := by
  simp only [certificateDifference, Array.map_push, Array.sum_push]
  congr 1
  simpa using s.expandAt_step 0

theorem Residual.expand_modify (b : Polynomial ℚ) (ns : Array (Polynomial K))
    (a : Polynomial K) (j : ℕ) (hj : j < ns.size) :
    (Residual.mk b (ns.modify j (· + a))).expand = (Residual.mk b ns).expand +
      (a : RatFunc K) / (b.map (algebraMap ℚ K) : RatFunc K) ^ (j + 1) := by
  dsimp only [Residual.expand]
  rw [← Fin.sum_congr' _ (Array.size_modify (xs := ns) (i := j) (f := (· + a))).symm]
  have he (i : Fin ns.size) :
      ((ns.modify j (· + a))[i.val] : RatFunc K) /
          (b.map (algebraMap ℚ K) : RatFunc K) ^ (i.val + 1) =
        (ns[i.val] : RatFunc K) / (b.map (algebraMap ℚ K) : RatFunc K) ^ (i.val + 1) +
          if i = ⟨j, hj⟩ then
            (a : RatFunc K) / (b.map (algebraMap ℚ K) : RatFunc K) ^ (j + 1) else 0 := by
    by_cases h : i = ⟨j, hj⟩
    · subst i
      simp [Array.getElem_modify, map_add, add_div]
    · have h' : j ≠ i.val := by intro he; apply h; exact Fin.ext he.symm
      simp [Array.getElem_modify, h, h']
  calc
    _ = ∑ i : Fin ns.size,
        ((ns[i.val] : RatFunc K) / (b.map (algebraMap ℚ K) : RatFunc K) ^ (i.val + 1) +
          if i = ⟨j, hj⟩ then
            (a : RatFunc K) / (b.map (algebraMap ℚ K) : RatFunc K) ^ (j + 1) else 0) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem Residual.expand_replicate (b : Polynomial ℚ) (n : ℕ) :
    (Residual.mk b (Array.replicate n (0 : Polynomial K))).expand = 0 := by
  simp [Residual.expand]

omit [Algebra ℚ K] in
theorem divByMonic_degree_pow_lt (f A : Polynomial K) (hf : f.Monic) (n : ℕ)
    (hA : A.degree < (f ^ (n + 1)).degree) :
    (A /ₘ f).degree < (f ^ n).degree := by
  by_cases h : A.degree < f.degree
  · rw [(divByMonic_eq_zero_iff hf).mpr h, degree_zero]
    exact WithBot.bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (pow_ne_zero _ hf.ne_zero))
  · have he := degree_add_divByMonic hf (le_of_not_gt h)
    rw [pow_succ, hf.degree_mul] at hA
    rw [add_comm (f ^ n).degree] at hA
    rw [← he] at hA
    exact (WithBot.add_lt_add_iff_left (degree_ne_bot.mpr hf.ne_zero)).mp hA

omit [Algebra ℚ K] in
theorem fraction_division_step (f A : Polynomial K) (hf : f ≠ 0) (n : ℕ) :
    ((A %ₘ f : Polynomial K) : RatFunc K) / (f : RatFunc K) ^ (n + 1) +
      ((A /ₘ f : Polynomial K) : RatFunc K) / (f : RatFunc K) ^ n =
      (A : RatFunc K) / (f : RatFunc K) ^ (n + 1) := by
  have hf' : (f : RatFunc K) ≠ 0 := by simpa using hf
  have he := congrArg (algebraMap K[X] (RatFunc K)) (modByMonic_add_div A f)
  simp only [map_add, map_mul] at he
  rw [pow_succ]
  field_simp
  exact he

theorem shifted_digit_fraction (b : Polynomial ℚ) (a : Polynomial K) (h : ℤ) (k : ℕ) :
    (ShiftSum.mk (taylor ((-h : ℤ) : K) a) (b ^ k) h.toNat).fractionAt (h : K) =
      (a : RatFunc K) / ((taylor (h : K) (b.map (algebraMap ℚ K)) : Polynomial K) : RatFunc K) ^ k := by
  simp [ShiftSum.fractionAt, taylor_taylor, Polynomial.map_pow, map_pow]

theorem shifted_digit_zero (b : Polynomial ℚ) (a : Polynomial K) (h : ℤ) (k : ℕ) :
    (ShiftSum.mk (taylor ((-h : ℤ) : K) a) (b ^ k) h.toNat).fractionAt 0 =
      ((taylor ((-h : ℤ) : K) a : Polynomial K) : RatFunc K) /
        (b.map (algebraMap ℚ K) : RatFunc K) ^ k := by
  simp [ShiftSum.fractionAt, Polynomial.map_pow, map_pow]

namespace Model

/-- One digit moves its translated fraction into the certificate and the residual. -/
theorem digit_value (g : PreparedGroup) (o : PreparedOccurrence)
    (ho : o.factor = taylor (o.shift : ℚ) g.base) (hh : 0 ≤ o.shift)
    (hm : g.base.Monic) (s : Array (ShiftSum K) × Array (Polynomial K) × Polynomial K)
    (j : ℕ) (hj : j < o.multiplicity) (hs : o.multiplicity ≤ s.2.1.size) :
    let z := digit g o s j
    certificateDifference z.1 + (Residual.mk g.base z.2.1).expand +
      (z.2.2 : RatFunc K) / (o.factor.map (algebraMap ℚ K) : RatFunc K) ^ (o.multiplicity - j - 1) =
    certificateDifference s.1 + (Residual.mk g.base s.2.1).expand +
      (s.2.2 : RatFunc K) / (o.factor.map (algebraMap ℚ K) : RatFunc K) ^ (o.multiplicity - j) := by
  have hk : o.multiplicity - j - 1 + 1 = o.multiplicity - j := by omega
  have hsize : o.multiplicity - j - 1 < s.2.1.size := by omega
  have hf : (o.factor.map (algebraMap ℚ K)).Monic := by
    rw [ho]
    exact (show (taylor (o.shift : ℚ) g.base).Monic by simpa [Monic] using hm).map _
  have he := fraction_division_step (o.factor.map (algebraMap ℚ K)) s.2.2 hf.ne_zero
    (o.multiplicity - j - 1)
  rw [hk] at he
  dsimp only [digit]
  split
  · rw [certificateDifference_push, Residual.expand_modify _ _ _ _ hsize, hk]
    have hc : (o.shift.toNat : K) = (o.shift : K) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : K)) (Int.toNat_of_nonneg hh)
    rw [hc, shifted_digit_fraction, shifted_digit_zero]
    have ht : taylor (o.shift : K) (g.base.map (algebraMap ℚ K)) =
        o.factor.map (algebraMap ℚ K) := by simp [ho, map_taylor]
    rw [ht]
    linear_combination he
  · have hz : o.shift = 0 := by omega
    rw [Residual.expand_modify _ _ _ _ hsize, hk]
    simp only [hz, neg_zero, Int.cast_zero, taylor_zero] at ho ⊢
    rw [← ho]
    linear_combination he

@[simp] theorem digit_size (g : PreparedGroup) (o : PreparedOccurrence)
    (s : Array (ShiftSum K) × Array (Polynomial K) × Polynomial K) (j : ℕ) :
    (digit g o s j).2.1.size = s.2.1.size := by
  unfold digit
  split <;> simp

@[simp] theorem digit_remainder (g : PreparedGroup) (o : PreparedOccurrence)
    (s : Array (ShiftSum K) × Array (Polynomial K) × Polynomial K) (j : ℕ) :
    (digit g o s j).2.2 = s.2.2 /ₘ o.factor.map (algebraMap ℚ K) := by
  unfold digit
  split <;> rfl

/-- The complete extraction loop consumes the entire proper numerator. -/
theorem occurrence_value (N : Polynomial K) (g : PreparedGroup) (o : PreparedOccurrence)
    (ho : o.factor = taylor (o.shift : ℚ) g.base)
    (hp : o.power = o.factor ^ o.multiplicity) (hh : 0 ≤ o.shift)
    (hm : g.base.Monic) (s : Array (ShiftSum K) × Array (Polynomial K))
    (hs : o.multiplicity ≤ s.2.size) :
    let z := occurrence N g s o
    z.2.size = s.2.size ∧
    certificateDifference z.1 + (Residual.mk g.base z.2).expand =
      certificateDifference s.1 + (Residual.mk g.base s.2).expand +
        (((N * o.inverse.map (algebraMap ℚ K)) %ₘ o.power.map (algebraMap ℚ K) : Polynomial K) : RatFunc K) /
          (o.power.map (algebraMap ℚ K) : RatFunc K) := by
  let f := o.factor.map (algebraMap ℚ K)
  let A := (N * o.inverse.map (algebraMap ℚ K)) %ₘ o.power.map (algebraMap ℚ K)
  have hf : f.Monic := by
    dsimp [f]
    rw [ho]
    exact (show (taylor (o.shift : ℚ) g.base).Monic by simpa [Monic] using hm).map _
  have hpower : o.power.map (algebraMap ℚ K) = f ^ o.multiplicity := by simp [hp, f]
  let run := fun n => (List.range n).foldl (digit g o) (s.1, s.2, A)
  have hinv (n : ℕ) (hn : n ≤ o.multiplicity) :
      (run n).2.1.size = s.2.size ∧
      (run n).2.2.degree < (f ^ (o.multiplicity - n)).degree ∧
      certificateDifference (run n).1 + (Residual.mk g.base (run n).2.1).expand +
        ((run n).2.2 : RatFunc K) / (f : RatFunc K) ^ (o.multiplicity - n) =
      certificateDifference s.1 + (Residual.mk g.base s.2).expand +
        (A : RatFunc K) / (f : RatFunc K) ^ o.multiplicity := by
    induction n with
    | zero =>
      refine ⟨rfl, ?_, ?_⟩
      · simpa [run, A, hpower] using
          degree_modByMonic_lt (N * o.inverse.map (algebraMap ℚ K)) (hf.pow o.multiplicity)
      · simp [run]
    | succ n ih =>
      obtain ⟨hsize, hdeg, hval⟩ := ih (by omega)
      have hj : n < o.multiplicity := by omega
      have hk : o.multiplicity - n - 1 + 1 = o.multiplicity - n := by omega
      have hnext : run (n + 1) = digit g o (run n) n := by
        simp [run, List.range_succ, List.foldl_append]
      rw [hnext]
      refine ⟨by simpa using hsize, ?_, ?_⟩
      · rw [digit_remainder]
        have hd := divByMonic_degree_pow_lt f (run n).2.2 hf
          (o.multiplicity - n - 1) (by simpa only [hk] using hdeg)
        simpa only [Nat.sub_sub] using hd
      · have hv := digit_value g o ho hh hm (run n) n hj (by omega)
        simpa only [Nat.sub_sub] using hv.trans hval
  obtain ⟨hsize, hdeg, hval⟩ := hinv o.multiplicity le_rfl
  have hz : (run o.multiplicity).2.2 = 0 := by
    simpa using hdeg
  refine ⟨hsize, ?_⟩
  simp only [Nat.sub_self, hz] at hval
  simpa [occurrence, run, A, hpower] using hval

end Model
end Gosper.RationalSum
