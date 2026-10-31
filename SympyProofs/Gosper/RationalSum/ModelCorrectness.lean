module

public import SympyProofs.Gosper.RationalSum.Reconstruction
public import SympyProofs.Gosper.RationalSum.Residuals
public import SympyProofs.Gosper.Summability

/-! Soundness and completeness of the proof-only reduction model. -/

@[expose] public section
noncomputable section
namespace Gosper.RationalSum
open Polynomial
open scoped Classical
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The fold model satisfies `P/D = ΔG + residual`. -/
theorem model_sound {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial K) : (Model.result (prepare D d) P).Sound P D := by
  let p := prepare D d
  let M := p.monicDenominator.map (algebraMap ℚ K)
  let A := C (algebraMap ℚ K p.coefficient⁻¹) * P
  have hm : M.Monic := (prepare_monic hd).denominator.map _
  have hM : (M : RatFunc K) ≠ 0 := by simpa using hm.ne_zero
  have hp := prepared_partialFractions hd (A %ₘ M) (degree_modByMonic_lt A hm)
  change (A %ₘ M : RatFunc K) / (M : RatFunc K) = _ at hp
  have hdiv : (A : RatFunc K) / (M : RatFunc K) =
      (A /ₘ M : RatFunc K) + (A %ₘ M : RatFunc K) / (M : RatFunc K) := by
    have he := congrArg (algebraMap K[X] (RatFunc K)) (modByMonic_add_div A M)
    simp only [map_add, map_mul] at he
    field_simp
    simpa only [RatFunc.coePolynomial, add_comm, mul_comm] using he.symm
  have hn : (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K) =
      (A : RatFunc K) / (M : RatFunc K) := by
    have hc : (C (algebraMap ℚ K D.leadingCoeff⁻¹) : RatFunc K) ≠ 0 := by
      have hz : algebraMap ℚ K D.leadingCoeff⁻¹ ≠ 0 := by
        simpa using (algebraMap ℚ K).injective.ne
          (inv_ne_zero (leadingCoeff_ne_zero.mpr hd.nonzero))
      change (algebraMap K[X] (RatFunc K)) (C (algebraMap ℚ K D.leadingCoeff⁻¹)) ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective K[X] (RatFunc K)).ne
        (C_ne_zero.mpr hz)
    dsimp only [A, M, p]
    rw [prepare_eq_model]
    simp only [Polynomial.map_mul, Polynomial.map_C, RatFunc.coePolynomial, map_mul]
    exact (mul_div_mul_left _ _ hc).symm
  unfold Result.Sound
  rw [model_reconstruct _ (prepare_groups_valid hd), ← hp]
  exact hn.trans hdiv

theorem Result.residualPart_eq_zero {r : Result K} (h : r.residualVanishes) :
    r.residualPart = 0 := by
  unfold Result.residualPart
  rw [← Array.sum_toList]
  apply List.sum_eq_zero
  intro v hv
  simp only [Array.toList_map, List.mem_map] at hv
  obtain ⟨g, hg, rfl⟩ := hv
  unfold Residual.expand
  apply Finset.sum_eq_zero
  intro i _
  have ha := h g (by simpa using hg) g.numerators[i.val] (Array.getElem_mem _)
  simp [ha]

theorem ShiftSum.fractionAt_shift (s : ShiftSum K) (a h : K) :
    Gosper.rationalShift a (s.fractionAt h) = s.fractionAt (h + a) := by
  simp only [ShiftSum.fractionAt, RatFunc.coePolynomial, map_div₀,
    Gosper.rationalShift_polynomial, taylor_taylor, add_comm a h]

theorem ShiftSum.expandAt_shift (s : ShiftSum K) (a h : K) :
    Gosper.rationalShift a (s.expandAt h) = s.expandAt (h + a) := by
  simp only [ShiftSum.expandAt, map_sum, ShiftSum.fractionAt_shift]
  simp only [add_assoc, add_comm]

theorem Result.primitiveAt_shift (r : Result K) (a h : K) :
    Gosper.rationalShift a (r.primitiveAt h) = r.primitiveAt (h + a) := by
  simp only [Result.primitiveAt, map_add, RatFunc.coePolynomial,
    Gosper.rationalShift_polynomial, taylor_taylor, add_comm a h,
    ← Array.sum_toList, Array.toList_map, map_list_sum, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro s hs
  exact s.expandAt_shift a h

/-- Vanishing residual coefficients give an actual rational antidifference. -/
theorem model_summable_of_residualVanishes
    {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d)
    (P : Polynomial K) (hz : (Model.result (prepare D d) P).residualVanishes) :
    ∃ G : RatFunc K,
      Gosper.rationalShift 1 G - G = (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K) := by
  refine ⟨(Model.result (prepare D d) P).primitiveAt 0, ?_⟩
  have h := model_sound hd P
  unfold Result.Sound at h
  rw [Result.residualPart_eq_zero hz, add_zero] at h
  simpa only [Result.primitiveAt_shift, zero_add] using h.symm

/-- Completeness: any rational antidifference forces every computed residual
numerator to vanish. The antidifference need not be the one computed by `Model.result`. -/
theorem model_residualVanishes_of_summable
    {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)} (hd : ShiftlessDecomposition.Valid D d)
    (P : Polynomial K)
    (h : ∃ G : RatFunc K,
      Gosper.rationalShift 1 G - G = (P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) :
    (Model.result (prepare D d) P).residualVanishes := by
  let r := Model.result (prepare D d) P
  apply residualVanishes_of_summable r
    (fun a ha => (model_residual_base_valid hd P a ha).1)
    (fun a ha => (model_residual_base_valid hd P a ha).2)
    (model_residual_separated hd P) (model_residual_proper hd P)
  obtain ⟨G, hG⟩ := h
  refine ⟨G - r.primitiveAt 0, ?_⟩
  have hs := model_sound hd P
  change _ = r.primitiveAt 1 - r.primitiveAt 0 + r.residualPart at hs
  simp only [map_sub, Result.primitiveAt_shift, zero_add]
  linear_combination hG + hs

/-- An exact finite-sum identity in the rational-function field. Keeping the
starting point as `X` avoids any implicit assumptions about evaluation at poles. -/
theorem model_sum_range {D : Polynomial ℚ} {d : Array (ShiftlessDecomposition.Group ℚ)}
    (hd : ShiftlessDecomposition.Valid D d) (P : Polynomial K) (n : ℕ) :
    let r := Model.result (prepare D d) P
    ∑ k ∈ Finset.range n,
        Gosper.rationalShift (k : K) ((P : RatFunc K) / (D.map (algebraMap ℚ K) : RatFunc K)) =
      r.primitiveAt (n : K) - r.primitiveAt 0 +
        ∑ k ∈ Finset.range n, Gosper.rationalShift (k : K) r.residualPart := by
  let r := Model.result (prepare D d) P
  have h := model_sound hd P
  change _ = r.primitiveAt 1 - r.primitiveAt 0 + r.residualPart at h
  dsimp only
  simp_rw [h, map_add, map_sub, Result.primitiveAt_shift, zero_add, add_comm (1 : K)]
  rw [Finset.sum_add_distrib]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
    (Finset.sum_range_sub (fun k : ℕ => r.primitiveAt (k : K)) n)

end Gosper.RationalSum
