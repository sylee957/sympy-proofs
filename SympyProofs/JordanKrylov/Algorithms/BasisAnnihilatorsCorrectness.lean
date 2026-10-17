import SympyProofs.JordanKrylov.Algorithms.BasisAnnihilators

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
open scoped Std.WP

/-- If the cofactor alone does not annihilate, another copy of the current factor is necessary. -/
private theorem necessary_power {K : Type*} [Field K] {d c f g : K[X]} (r : ℕ)
    (hc : c.Monic) (hf : Irreducible f) (hcd : c ∣ d)
    (hyes : d ∣ c * (f ^ r * g)) (hno : ¬ d ∣ c * g) : c * f ∣ d := by
  obtain ⟨q, rfl⟩ := hcd
  have hq : q ∣ f ^ r * g := (mul_dvd_mul_iff_left hc.ne_zero).mp hyes
  have hn : ¬ q ∣ g := fun h => hno (mul_dvd_mul_left c h)
  have hfq : f ∣ q := by
    by_contra h
    exact hn ((hf.coprime_pow_of_not_dvd r h).dvd_of_dvd_mul_left hq)
  exact mul_dvd_mul_left c hfq

private theorem apply_mul (K : Subfield ℂ) [Operations K]
    (hops : Operations.IsCorrect K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (c p : K[X]) (v : Fin n → K) :
    Operations.applyMatrix p A (aeval A c *ᵥ v) = aeval A (c * p) *ᵥ v := by
  rw [hops.applyMatrix_eq, mul_comm c p, map_mul, mulVec_mulVec]

/-- Grouped factor searches compute the minimal annihilator of each input vector. -/
theorem computeBasisAnnihilators_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (factors : Array (K[X] × ℕ)) (e : Fin m → (Fin n → K))
    (hg : ∀ fm ∈ factors, fm.1.Monic ∧ Irreducible fm.1)
    (hfactorization : A.charpoly =
      (factors.toList.flatMap (fun fm => List.replicate fm.2 fm.1)).prod) :
    computeBasisAnnihilators K A factors e =
      Array.ofFn (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  let product := fun fs : List (K[X] × ℕ) => (fs.map (fun fm => fm.1 ^ fm.2)).prod
  generalize h : computeBasisAnnihilators K A factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ out => out = (pref.map (fun i => minimalAnnihilatingPolynomial K A (e i))).toArray
  · by
      let v := b0
      exact fun _ suff (b0, c, rest) =>
        (rest = suff ∨ b0 = 0) ∧ c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣ c * product rest
  · fun pref _ c => c = product pref
  · by
      let v := b0
      rename_i pref f exponent suff hsplit current c rest hi _ hn co hc
      exact fun pref _ (b0, c, probe) =>
        c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧ probe = aeval A (c * product remaining) *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣
          c * (f ^ (exponent - pref.length) * product remaining)
  case vc1 => rfl
  case vc2 =>
    rename_i out hout
    simpa only [← List.ofFn_eq_map, List.toArray_ofFn] using hout
  case vc3 =>
    simp only [remaining, candidate, hops.one_eq, Std.Internal.ForIn.toList_array,
      monic_one, one_dvd, map_one, one_mulVec, one_mul, true_or, true_and]
    apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
    have he : product factors.toList = A.charpoly := by
      simpa [product, List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def, List.prod_replicate] using hfactorization.symm
    rw [he, Matrix.aeval_self_charpoly, zero_mulVec]
  case vc4 =>
    rename_i pref i suff hsplit out hout current c rest hi _
    rcases hi with ⟨hr, hc, hd, hb, hcover⟩
    have he : c = minimalAnnihilatingPolynomial K A (e i) := by
      apply eq_of_monic_of_dvd_of_natDegree_le
        (minimalAnnihilatingPolynomial_monic K A (e i)) hc
      · rcases hr with hr | hz
        · simpa [hr, product] using hcover
        · exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hb.symm.trans hz)
      · exact natDegree_le_of_dvd hd (minimalAnnihilatingPolynomial_monic K A _).ne_zero
    apply Array.toList_inj.mp
    simp [result, hout, he]
  case vc6 =>
    simp [cofactor, hops.one_eq, product]
  case vc11 =>
    rename_i pref g exponent suff hsplit c hc
    simp [cofactor, hops.mul_eq, hops.pow_eq, hc, product]
  case vc7 =>
    rename_i pref f exponent suff hsplit current c rest hi _ hn co hc
    rcases hi with ⟨hr, hmon, hd, hb, hcover⟩
    have hr := hr.resolve_right hn
    refine ⟨hmon, hd, hb, ?_, ?_⟩
    · by_cases hempty : remaining = []
      · simp [probe, hempty, product, hb]
      · simp [probe, List.isEmpty_iff, hempty, hc, hb, apply_mul K hops]
    · simpa only [List.length_nil, Nat.sub_zero, remaining, hr,
        List.tail_cons, product, List.map_cons, List.prod_cons] using hcover
  case vc8 =>
    rename_i pref f exponent suff hsplit current c rest hi _ hn co hc nextB nextC nextProbe hnext _
    refine ⟨?_, hnext.1, hnext.2.1, hnext.2.2.1, ?_⟩
    · left
      simp only [remaining, hi.1.resolve_right hn, List.tail_cons]
    · simpa only [List.length_range, Nat.sub_self, pow_zero, one_mul] using hnext.2.2.2.2
  case vc9 =>
    rename_i current c probeValue hi _ hz
    refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
    simp only [List.length_range, Nat.sub_self, pow_zero, one_mul]
    exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
      (hi.2.2.2.1.symm.trans hz)
  case vc10 =>
    rename_i factorPref f exponent suffix hsplit oldB oldC rest houter _ hnonzero co hco _
      steps j tail hsteps current c probeValue hi _ hn
    have hf : f.Monic ∧ Irreducible f := by
      apply hg (f, exponent)
      rw [← Array.mem_toList_iff]
      simp only [Std.Internal.ForIn.toList_array] at hsplit
      rw [hsplit]
      simp
    have hlen : steps.length < exponent := by
      have hl := congrArg List.length hsteps
      simp only [List.length_range, List.length_append, List.length_cons] at hl
      omega
    have hnext := necessary_power (exponent - steps.length) hi.1 hf.2 hi.2.1
      hi.2.2.2.2 (fun hdiv => hn (hi.2.2.2.1.trans
        ((minimalAnnihilatingPolynomial_dvd_iff K A _ _).mp hdiv)))
    dsimp only [candidate, b0, probe]
    rw [hops.mul_eq]
    refine ⟨hi.1.mul hf.1, hnext, ?_, ?_, ?_⟩
    · rw [hi.2.2.1, apply_mul K hops]
    · rw [hi.2.2.2.1, apply_mul K hops, mul_right_comm c]
    · simp only [List.length_append, List.length_singleton]
      have hex : exponent - steps.length = (exponent - (steps.length + 1)) + 1 := by omega
      have he : c * f * (f ^ (exponent - (steps.length + 1)) * product remaining) =
          c * (f ^ (exponent - steps.length) * product remaining) := by
        rw [hex, pow_succ]
        ring
      rw [he]
      exact hi.2.2.2.2
  case vc5 =>
    rename_i current c rest hi _ hz
    exact ⟨Or.inr hz, hi.2⟩
end SympyProofs.JordanKrylov
