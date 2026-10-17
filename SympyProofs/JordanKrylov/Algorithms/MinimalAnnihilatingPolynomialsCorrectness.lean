import SympyProofs.JordanKrylov.Algorithms.MinimalAnnihilatingPolynomials
import Std.Tactic.Do
import Std.WP

namespace SympyProofs.JordanKrylov
open Polynomial Matrix
namespace AnnihilatorSearch

/-- A factor which first makes a prefix annihilate is necessary. -/
theorem necessary_factor {K : Type*} [Field K] {d c a t : K[X]}
    (hc : c.Monic) (ha : Irreducible a) (hcd : c ∣ d)
    (hyes : d ∣ c * (t * a)) (hno : ¬ d ∣ c * t) : c * a ∣ d := by
  obtain ⟨q, rfl⟩ := hcd
  have hq : q ∣ t * a := (mul_dvd_mul_iff_left hc.ne_zero).mp hyes
  have hn : ¬ q ∣ t := fun h => hno (mul_dvd_mul_left c h)
  have haq : a ∣ q := by
    by_contra h
    exact hn (((ha.coprime_iff_not_dvd.mpr h).symm).dvd_of_dvd_mul_right hq)
  exact mul_dvd_mul_left c haq

/-- If the cofactor alone does not annihilate, the next distinguished factor is necessary. -/
theorem necessary_power {K : Type*} [Field K] {d c f g : K[X]} (r : ℕ)
    (hc : c.Monic) (hf : Irreducible f) (hcd : c ∣ d)
    (hyes : d ∣ c * (f ^ r * g)) (hno : ¬ d ∣ c * g) : c * f ∣ d := by
  obtain ⟨q, rfl⟩ := hcd
  have hq : q ∣ f ^ r * g := (mul_dvd_mul_iff_left hc.ne_zero).mp hyes
  have hn : ¬ q ∣ g := fun h => hno (mul_dvd_mul_left c h)
  have hfq : f ∣ q := by
    by_contra h
    exact hn ((hf.coprime_pow_of_not_dvd r h).dvd_of_dvd_mul_left hq)
  exact mul_dvd_mul_left c hfq

theorem apply_mul (K : Subfield ℂ) [Operations K]
    (hops : Operations.IsCorrect K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (c p : K[X]) (v : Fin n → K) :
    Operations.applyMatrix p A (aeval A c *ᵥ v) = aeval A (c * p) *ᵥ v := by
  rw [hops.applyMatrix_eq, mul_comm c p, map_mul, mulVec_mulVec]

end AnnihilatorSearch

open AnnihilatorSearch
open scoped Std.WP in
/-- Algorithm 7 computes the minimal annihilator of every input vector.
The product bound can come from the minimal or characteristic polynomial;
no spanning assumption on the supplied family is needed. -/
theorem computeMinimalAnnihilatingPolynomials_correct
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (bound : ℕ)
    (factors : Array K[X]) (e : Fin m → (Fin n → K))
    (hf : f.Monic) (hfi : Irreducible f)
    (hg : ∀ g ∈ factors, g.Monic ∧ Irreducible g)
    (hbound : aeval A (f ^ bound * factors.toList.prod) = 0) :
    computeMinimalAnnihilatingPolynomials K A f bound factors e =
      Array.ofFn (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  generalize h : computeMinimalAnnihilatingPolynomials K A f bound factors e = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ product => product = pref.prod
  · fun pref _ out => out = (pref.map (fun i => minimalAnnihilatingPolynomial K A (e i))).toArray
  · by
      let v := b0
      exact fun pref _ (b, b0, c) =>
        (pref = List.range bound ∧ c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
          b0 = aeval A c *ᵥ v ∧
          minimalAnnihilatingPolynomial K A v ∣ c * factors.toList.prod) ∨
        (f ^ pref.length ∣ minimalAnnihilatingPolynomial K A v ∧
          b0 = aeval A (f ^ pref.length) *ᵥ v ∧
          b = aeval A (f ^ pref.length * factors.toList.prod) *ᵥ v ∧ b ≠ 0)
  · by
      let v := b0
      exact fun pref _ (b0, c, iMax) =>
        c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣ c * (factors.toList.take iMax.val).prod ∧
        (b0 = 0 ∨ iMax.val ≤ factors.toList.length - pref.length)
  · by
      let v := b0
      rename_i current c limit hi _ hn
      exact fun pref _ (b0, candidate, iMax, probe) =>
        (pref = List.finRange (limit.val) ∧ candidate.Monic ∧
          candidate ∣ minimalAnnihilatingPolynomial K A v ∧
          b0 = aeval A candidate *ᵥ v ∧
          minimalAnnihilatingPolynomial K A v ∣ candidate * (factors.toList.take iMax.val).prod ∧
          iMax.val < limit.val) ∨
        (b0 = current ∧ candidate = c ∧ iMax = limit ∧
          probe = aeval A (c * (factors.toList.take pref.length).prod) *ᵥ v ∧ probe ≠ 0)
  · by
      let v := b0
      exact fun pref _ (b0, c, iMax) =>
        c.Monic ∧ c ∣ minimalAnnihilatingPolynomial K A v ∧
        b0 = aeval A c *ᵥ v ∧
        minimalAnnihilatingPolynomial K A v ∣ c * (factors.toList.take iMax.val).prod ∧
        (b0 = 0 ∨ iMax.val ≤ factors.toList.length - pref.length)
  · by
      let v := b0
      rename_i current c limit hi _ hn
      exact fun pref _ (b0, candidate, iMax, probe) =>
        (pref = List.finRange (limit.val) ∧ candidate.Monic ∧
          candidate ∣ minimalAnnihilatingPolynomial K A v ∧
          b0 = aeval A candidate *ᵥ v ∧
          minimalAnnihilatingPolynomial K A v ∣ candidate * (factors.toList.take iMax.val).prod ∧
          iMax.val < limit.val) ∨
        (b0 = current ∧ candidate = c ∧ iMax = limit ∧
          probe = aeval A (c * (factors.toList.take pref.length).prod) *ᵥ v ∧ probe ≠ 0)
  case vc1 => exact hops.one_eq
  case vc2 => rfl
  case vc3 =>
    rename_i out hi
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    simpa only [← List.ofFn_eq_map, List.toArray_ofFn] using hi
  case vc6 =>
    rename_i pref i suff hsplit out hout _ _ oldB oldB0 oldC hfirst _ current c rest hi _
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    rcases hi with ⟨hc, hd, hb0, hrest, hz | hlen⟩ <;>
      have hfinal : c = minimalAnnihilatingPolynomial K A (e i) := by
        apply eq_of_monic_of_dvd_of_natDegree_le
          (minimalAnnihilatingPolynomial_monic K A (e i)) hc
        · first
          | exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hb0.symm.trans hz)
          | have he : rest.val = 0 := by omega
            simpa only [he, List.take_zero, List.prod_nil, mul_one] using hrest
        · exact natDegree_le_of_dvd hd (minimalAnnihilatingPolynomial_monic K A _).ne_zero
    all_goals
      dsimp only [result]
      apply Array.toList_inj.mp
      simp only [Array.toList_push, hout, hfinal, List.map_append, List.map_singleton]
  case vc21 =>
    rename_i pref g suff hsplit product hproduct
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    dsimp only [cofactor]
    simp only [hops.mul_eq, hproduct, List.prod_append, List.prod_singleton]

  case vc15 =>
    rename_i pref i suff hsplit out hout _ _ current c rest hi _
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    rcases hi with ⟨hc, hd, hb0, hrest, hz | hlen⟩ <;>
      have hfinal : c = minimalAnnihilatingPolynomial K A (e i) := by
        apply eq_of_monic_of_dvd_of_natDegree_le
          (minimalAnnihilatingPolynomial_monic K A (e i)) hc
        · first
          | exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hb0.symm.trans hz)
          | have he : rest.val = 0 := by omega
            simpa only [he, List.take_zero, List.prod_nil, mul_one] using hrest
        · exact natDegree_le_of_dvd hd (minimalAnnihilatingPolynomial_monic K A _).ne_zero
    all_goals
      dsimp only [result]
      apply Array.toList_inj.mp
      simp only [Array.toList_push, hout, hfinal, List.map_append, List.map_singleton]
  case vc4 =>
    rename_i product hproduct pref i suff hsplit out hout _ hn
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    right
    simpa only [List.length_nil, pow_zero, one_dvd, map_one, one_mulVec, one_mul,
      true_and, b, b0, hproduct, hops.applyMatrix_eq] using hn
  case vc5 =>
    rename_i oldB oldB0 c hi _
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    rcases hi with ⟨_, hc, hd, hb0, hrest⟩ | ⟨_, _, hb, hn⟩
    · exact ⟨hc, hd, hb0, by simpa only [iMax, ← Array.length_toList, List.take_length] using hrest, Or.inr (by simp [iMax])⟩
    · exact (hn (by simpa only [List.length_range, hbound, zero_mulVec] using hb)).elim
  case vc12 | vc13 =>
    rename_i pref k suff hsplit oldB oldB0 c hi _ hz
    have hp : pref.length < bound := by
      have hl := congrArg List.length hsplit
      simp only [List.length_range, List.length_append, List.length_cons] at hl
      omega
    rcases hi with h | ⟨hd, hb0, hb, hn⟩
    · have hl := congrArg List.length h.1
      simp only [List.length_range] at hl
      omega
    have hk : k = pref.length := by
      have he := congrArg (fun xs => xs[pref.length]?) hsplit
      simpa [List.getElem?_append, hp] using he.symm
    have hcover : ∀ v : Fin n → K, minimalAnnihilatingPolynomial K A v ∣
        f ^ pref.length * (f ^ (bound - pref.length) * factors.toList.prod) := by
      intro v
      apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hp), hbound, zero_mulVec]
    have hnext := necessary_power (bound - pref.length) (hf.pow pref.length) hfi hd (hcover _)
      (fun h => hn (hb.trans ((minimalAnnihilatingPolynomial_dvd_iff K A _ _).mp h)))
    rw [← pow_succ] at hnext
    have hbnext := congrArg (Operations.applyMatrix f A) hb
    rw [apply_mul K hops, mul_right_comm, ← pow_succ] at hbnext
    have hb0next := congrArg (Operations.applyMatrix f A) hb0
    rw [apply_mul K hops, ← pow_succ] at hb0next
    first
    | left
      dsimp only [candidate, b0]
      rw [hops.pow_eq, hk]
      exact ⟨rfl, hf.pow _, hnext, hb0next,
        (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr (hbnext.symm.trans hz)⟩
    | right
      simpa only [List.length_append, List.length_singleton] using
        And.intro hnext ⟨hb0next, hbnext, hz⟩
  case vc14 =>
    rename_i product hproduct pref i suff hsplit out hout _ hz
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    have hb : aeval A factors.toList.prod *ᵥ e i = 0 := by
      simpa only [b, hproduct, hops.applyMatrix_eq, not_not] using hz
    simp only [iMax, ← Array.length_toList, List.take_length, candidate, b0, hops.one_eq, monic_one, one_dvd, map_one, one_mulVec,
      one_mul, List.length_nil, Nat.sub_zero, le_refl, or_true, and_true, true_and]
    exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr hb

  case vc7 | vc16 =>
    rename_i pref g suff hsplit current c limit hi _ hz
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, ?_⟩
    rcases hz with hz | hz
    · exact Or.inr (by simp [hz])
    · exact Or.inl hz
  case vc8 | vc17 =>
    rename_i current c limit hi _ hn
    right
    refine ⟨rfl, rfl, rfl, ?_, fun h => hn (Or.inr h)⟩
    simpa only [List.length_nil, List.take_zero, List.prod_nil, mul_one] using hi.2.2.1
  case vc9 | vc18 =>
    rename_i pref g suff hsplit current c limit hi _ hn nextB nextC nextMax probe hs _ _
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    rcases hs with ⟨_, hc, hd, hb, hcover, hlt⟩ | ⟨_, _, _, hb, hz⟩
    · refine ⟨hc, hd, hb, hcover, Or.inr ?_⟩
      have hlen := hi.2.2.2.2.resolve_left (fun h => hn (Or.inr h))
      have hp : pref.length < factors.toList.length := by
        rw [hsplit, List.length_append, List.length_cons]; omega
      simp only [List.length_append, List.length_singleton]
      omega
    · apply (hz _).elim
      rw [hb, List.length_finRange]
      exact (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mp hi.2.2.2.1
  case vc10 | vc19 | vc11 | vc20 =>
    rename_i current c limit houter _ hcurrent pref j suff hsplit nextB nextC nextMax oldProbe hi _ _ hz
    simp (config := { zeta := false, dsimp := false }) only [Std.Internal.ForIn.toList_array] at *
    have hp : pref.length < limit.val := by
      have hl := congrArg List.length hsplit
      simp only [List.length_finRange, ← Array.length_toList, List.length_append, List.length_cons] at hl
      omega
    rcases hi with h | ⟨hb0, hc, hm, hb, hn⟩
    · have hl := congrArg List.length h.1
      simp only [List.length_finRange] at hl
      omega
    subst nextB
    subst nextC
    subst nextMax
    have hj : j.val = pref.length := by
      have he := congrArg (fun xs => xs[pref.length]?.map Fin.val) hsplit
      simpa [List.finRange, List.getElem?_append, ← Array.length_toList, hp] using he.symm
    have hidx : j.val < factors.toList.length :=
      Nat.lt_of_lt_of_le j.isLt limit.property
    have hfactor : g.Monic ∧ Irreducible g := by
      apply hg
      simpa only [g] using Array.getElem_mem hidx
    have htake : (factors.toList.take (pref.length + 1)).prod =
        (factors.toList.take pref.length).prod * g := by
      rw [← hj, List.take_succ_eq_append_getElem hidx]
      simp only [List.prod_append, List.prod_singleton, g, Array.getElem_toList]
    have he := congrArg (Operations.applyMatrix g A) hb
    rw [apply_mul K hops] at he
    first
    | left
      dsimp only [candidate, b0, iMax]
      rw [hops.mul_eq]
      refine ⟨True.intro, houter.1.mul hfactor.1, ?_, ?_, ?_, j.isLt⟩
      · apply necessary_factor houter.1 hfactor.2 houter.2.1
        · apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
          simpa only [mul_assoc] using he.symm.trans hz
        · intro h
          exact hn (hb.trans ((minimalAnnihilatingPolynomial_dvd_iff K A _ _).mp h))
      · rw [houter.2.2.1, apply_mul K hops]
      · apply (minimalAnnihilatingPolynomial_dvd_iff K A _ _).mpr
        simpa only [hj, mul_right_comm c g] using he.symm.trans hz
    | right
      refine ⟨rfl, rfl, rfl, ?_, hz⟩
      simpa only [List.length_append, List.length_singleton, htake, mul_assoc] using he


/-- The characteristic exponent is always a sufficient bound, by Cayley–Hamilton. -/
theorem computeMinimalAnnihilatingPolynomials_correct_of_charpoly
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (bound : ℕ)
    (factors : Array K[X]) (e : Fin m → (Fin n → K))
    (hf : f.Monic) (hfi : Irreducible f)
    (hg : ∀ g ∈ factors, g.Monic ∧ Irreducible g)
    (hfactorization : A.charpoly = f ^ bound * factors.toList.prod) :
    computeMinimalAnnihilatingPolynomials K A f bound factors e =
      Array.ofFn (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  apply computeMinimalAnnihilatingPolynomials_correct K hops A f bound factors e hf hfi hg
  rw [← hfactorization]
  exact Matrix.aeval_self_charpoly A

/-- The paper's smaller bound is valid when the product is the minimal polynomial. -/
theorem computeMinimalAnnihilatingPolynomials_correct_of_minpoly
    (K : Subfield ℂ) [DecidableEq K] [Operations K]
    (hops : Operations.IsCorrect K) {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (f : K[X]) (bound : ℕ)
    (factors : Array K[X]) (e : Fin m → (Fin n → K))
    (hf : f.Monic) (hfi : Irreducible f)
    (hg : ∀ g ∈ factors, g.Monic ∧ Irreducible g)
    (hfactorization : minpoly K A = f ^ bound * factors.toList.prod) :
    computeMinimalAnnihilatingPolynomials K A f bound factors e =
      Array.ofFn (fun i => minimalAnnihilatingPolynomial K A (e i)) := by
  apply computeMinimalAnnihilatingPolynomials_correct K hops A f bound factors e hf hfi hg
  rw [← hfactorization]
  exact minpoly.aeval K A

end SympyProofs.JordanKrylov
