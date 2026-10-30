module

public import SympyProofs.Gosper.ModularShifts.Bounds
public import SympyProofs.Gosper.ModularShifts.Precision
public import SympyProofs.Gosper.ModularShifts.Matching
public import SympyProofs.Gosper.ModularShifts.Verification

/-! Soundness and completeness of modular shift enumeration. -/

@[expose] public section
noncomputable section
namespace Gosper.ModularShifts
open Polynomial

private theorem gcd_monic (p q : Polynomial ℚ) (hp : p ≠ 0) :
    (GCDMonoid.gcd p q).Monic := by
  rw [← normalize_gcd]
  exact monic_normalize (fun h => hp ((gcd_eq_zero_iff p q).mp h).1)

private theorem gcd_ne_one_iff (p q : Polynomial ℚ) (hp : p ≠ 0) :
    GCDMonoid.gcd p q ≠ 1 ↔ ¬IsCoprime p q := by
  exact (not_congr (gcd_monic p q hp).isUnit_iff).symm.trans
    (not_congr (gcd_isUnit_iff p q))

/-- A genuine rational overlap yields a pair of translated Hensel factors.
This derives coverage from divisibility and unique-lifting compatibility. -/
theorem overlapping_factors (ops : Backend) (r e : ℕ) (Good : Polynomial ℚ → Prop)
    (laws : FactorizationLaws ops r e Good) (p q : Polynomial ℚ)
    (hp : p ≠ 0) (hpg : Good p) (hqg : Good q) (h : ℤ)
    (hov : ¬IsCoprime p (taylor (h : ℚ) q)) :
    ∃ g ∈ factors ops r e q, taylor (h : ZMod (r ^ e)) g ∈ factors ops r e p := by
  let d := GCDMonoid.gcd p (taylor (h : ℚ) q)
  have hdm : d.Monic := gcd_monic p _ hp
  have hdp : d ∣ p := gcd_dvd_left _ _
  have hdt : d ∣ taylor (h : ℚ) q := gcd_dvd_right _ _
  have hdg : Good d := laws.divisor_good hpg hdm hdp
  have hdpos : 0 < d.natDegree := by
    have hd1 : d ≠ 1 := (gcd_ne_one_iff p _ hp).mpr hov
    exact Nat.pos_of_ne_zero (fun hz => hd1 (hdm.natDegree_eq_zero.mp hz))
  let d' := taylor (-h : ℚ) d
  have hem : d'.Monic := by simpa [d', Monic] using hdm
  have heg : Good d' := by simpa [d'] using laws.translate_good hdg (-h)
  have heq : d' ∣ q := by
    simpa [d', taylor_taylor] using (taylorAlgHom (-h : ℚ)).toRingHom.map_dvd hdt
  have hep : 0 < d'.natDegree := by simpa [d'] using hdpos
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ (laws.nonempty heg hep)
  have hge : g ∈ factors ops r e d' := Array.mem_toList_iff.mp hg
  refine ⟨g, laws.divides hqg hem heq g hge, ?_⟩
  apply laws.divides hpg hdm hdp
  simpa [d', taylor_taylor] using laws.translate heg h g hge

/-- The initial degree check returns before any backend operation is used. -/
theorem shifts_eq_empty_of_natDegree_eq_zero (ops : Backend) (p q : Polynomial ℚ)
    (hd : p.natDegree = 0 ∨ q.natDegree = 0) : shifts ops p q = #[] := by
  simp [shifts, hd]

/-- No false positives and no missed integer shifts for monic square-free inputs,
under the supplied backend contracts. These preconditions are used only in proofs. -/
theorem mem_shifts (ops : Backend) (hops : ops.Valid) (p q : Polynomial ℚ)
    (hp : p.Monic) (hq : q.Monic) (hps : Squarefree p) (hqs : Squarefree q) (h : ℤ) :
    h ∈ shifts ops p q ↔ ¬IsCoprime p (taylor (h : ℚ) q) := by
  by_cases hpd : p.natDegree = 0
  · rw [shifts_eq_empty_of_natDegree_eq_zero ops p q (Or.inl hpd)]
    simp [hp.natDegree_eq_zero.mp hpd, isCoprime_one_left]
  by_cases hqd : q.natDegree = 0
  · rw [shifts_eq_empty_of_natDegree_eq_zero ops p q (Or.inr hqd)]
    simp [hq.natDegree_eq_zero.mp hqd, isCoprime_one_right]
  simp only [shifts, hpd, hqd, or_self]
  let P := (clearDenominators p).primPart
  let Q := (clearDenominators q).primPart
  let r := firstPrimeAvoiding (max p.natDegree q.natDegree)
    (excludedDivisors ops P * excludedDivisors ops Q)
  let e := Nat.log r (2 * ⌈radius p + radius q⌉₊) + 1
  change h ∈ matchFactors P Q (factors ops r e p) (factors ops r e q) ↔ _
  rw [(matchFactors_spec P Q (factors ops r e p) (factors ops r e q)).2 h]
  constructor
  · rintro ⟨f, hf, g, hg, _, _, _, hcheck⟩
    exact (integer_shift_overlap_iff p q hp hq h).mp hcheck
  · intro hov
    obtain ⟨hprime, hexp, hdegree, hbound, hpr, hqr⟩ :=
      precision_spec ops hops.resultant_valid p q ⌈radius p + radius q⌉₊ hp hq hps hqs hpd hqd
    obtain ⟨Good, hpg, hqg, laws⟩ :=
      hops.lifting_valid p q r e hp hq hps hqs hprime hexp hdegree hpr hqr
    obtain ⟨g, hg, hf⟩ :=
      overlapping_factors ops r e Good laws p q hp.ne_zero hpg hqg h hov
    refine ⟨taylor (h : ZMod (r ^ e)) g, hf, g, hg, ?_⟩
    refine ⟨natDegree_taylor _ _, center_taylor g (laws.monic hqg g hg)
      (laws.positive_degree hqg g hg) (laws.degree_unit hqg g hg) _, ?_,
      (integer_shift_overlap_iff p q hp hq h).mpr hov⟩
    rw [candidate_residue g (laws.monic hqg g hg) (laws.positive_degree hqg g hg)
      (laws.degree_unit hqg g hg)]
    exact recover_integer (by omega) _ hbound h
      (abs_shift_le_bound p q hp.ne_zero hq.ne_zero h hov)

theorem nodup_shifts (ops : Backend) (p q : Polynomial ℚ) :
    (shifts ops p q).toList.Nodup := by
  by_cases hd : p.natDegree = 0 ∨ q.natDegree = 0
  · rw [shifts_eq_empty_of_natDegree_eq_zero ops p q hd]
    simp
  simp only [shifts, hd]
  exact (matchFactors_spec (clearDenominators p).primPart (clearDenominators q).primPart _ _).1

end Gosper.ModularShifts
